#include "Annotation.h"
#include "AstSerializer.h"
#include "CommentProcessor.h"
#include "ContextFreePPCallbacks.h"
#include "capnp/message.h"
#include "capnp/serialize.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "Context.h"
#ifdef _WIN32
#include <io.h>
#include <fcntl.h>
#endif

static llvm::cl::OptionCategory category("Verifast AST exporter options");

static llvm::cl::list<std::string> allowExpansions(
    "allow_macro_expansion",
    llvm::cl::desc("is a list of macros that are always allowed to expand."),
    llvm::cl::value_desc("macros"), llvm::cl::ZeroOrMore,
    llvm::cl::cat(category));

static llvm::cl::extrahelp
    commonHelp(clang::tooling::CommonOptionsParser::HelpMessage);

namespace vf {

using Builder = stubs::TU::Builder;

class VerifastASTConsumer : public clang::ASTConsumer {
  Builder &_builder;
  AnnotationStore &_store;
  const Context &_context;

public:
  void HandleTranslationUnit(clang::ASTContext &context) override {
    AstSerializer serializer(context, _store, _context);
    serializer.serializeTU(_builder, context.getTranslationUnitDecl());
  }

  explicit VerifastASTConsumer(Builder &builder, AnnotationStore &store, const Context &context)
      : _builder(builder), _store(store), _context(context) {}
  VerifastASTConsumer(Builder &&builder, AnnotationStore &&store) = delete;
};

class VerifastFrontendAction : public clang::ASTFrontendAction {
  Builder _builder;
  AnnotationStore _store;
  CommentProcessor _commentProcessor;
  Context _context;

public:
  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &compiler,
                    llvm::StringRef inFile) override {
    auto &PP = compiler.getPreprocessor();
    PP.addPPCallbacks(
        std::make_unique<ContextFreePPCallbacks>(_context, PP, allowExpansions));
    PP.addCommentHandler(&_commentProcessor);
    return std::make_unique<VerifastASTConsumer>(_builder, _store, _context);
  }

  explicit VerifastFrontendAction(Builder &&builder)
      : _builder(builder), _commentProcessor(_store) {}
};

using msg_builders = std::list<capnp::MallocMessageBuilder>;

class VerifastActionFactory : public clang::tooling::FrontendActionFactory {
  msg_builders &_builders;

public:
  std::unique_ptr<clang::FrontendAction> create() override {
    _builders.emplace_back();
    return std::make_unique<VerifastFrontendAction>(
        _builders.back().initRoot<stubs::TU>());
  }

  explicit VerifastActionFactory(msg_builders &builders)
      : _builders(builders) {}
  VerifastActionFactory(Builder &&builder) = delete;
};

} // namespace vf

int main(int argc, const char **argv) {
  auto expectedParser = clang::tooling::CommonOptionsParser::create(argc, argv, category);
  if (! expectedParser) {
    llvm::errs() << expectedParser.takeError();
  }
  clang::tooling::CommonOptionsParser &optionsParser = expectedParser.get();
  clang::tooling::ClangTool tool(optionsParser.getCompilations(),
                                 optionsParser.getSourcePathList());
#ifdef _WIN32                 
  _setmode(1, _O_BINARY);
#endif        
  vf::msg_builders msgBuilders;
  vf::VerifastActionFactory factory(msgBuilders);

  int err = tool.run(&factory);

  capnp::MallocMessageBuilder result;
  auto serResult = result.initRoot<stubs::SerResult>();
  if (err)
    serResult.setErr();
  else
    serResult.setOk();
  capnp::writeMessageToFd(1, result);

  if (!err) {
    for (auto &msg : msgBuilders) {
      // std::cout << "size: " << msg.sizeInWords() << std::endl;
      capnp::writeMessageToFd(1, msg);
    }
  }

  return err;
}
