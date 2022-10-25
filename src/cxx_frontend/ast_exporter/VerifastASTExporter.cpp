#include "Annotation.h"
#include "AstSerializer.h"
#include "CommentProcessor.h"
#include "ContextFreePPCallbacks.h"
#include "InclusionContext.h"
#include "capnp/message.h"
#include "capnp/serialize.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif

static llvm::cl::OptionCategory category("Verifast AST exporter options");

static llvm::cl::list<std::string> allowExpansions(
    "allow_macro_expansion",
    llvm::cl::desc(
        "Allow a set of macros to expand regardless of its context."),
    llvm::cl::value_desc("macros"), llvm::cl::ZeroOrMore,
    llvm::cl::CommaSeparated, llvm::cl::cat(category));

static llvm::cl::opt<bool> exportImplicitDecls(
    "export_implicit_decls",
    llvm::cl::desc("Enable exporting implicit declarations."),
    llvm::cl::cat(category));

static llvm::cl::extrahelp
    commonHelp(clang::tooling::CommonOptionsParser::HelpMessage);

namespace vf {

using Builder = stubs::TU::Builder;

class VerifastASTConsumer : public clang::ASTConsumer {
  Builder &m_builder;
  AnnotationStore &m_store;
  const InclusionContext &m_context;

public:
  void HandleTranslationUnit(clang::ASTContext &context) override {
    AstSerializer serializer(context, m_store, m_context, exportImplicitDecls);
    serializer.serializeTU(m_builder, context.getTranslationUnitDecl());
  }

  explicit VerifastASTConsumer(Builder &builder, AnnotationStore &store,
                               const InclusionContext &context)
      : m_builder(builder), m_store(store), m_context(context) {}
  VerifastASTConsumer(Builder &&builder, AnnotationStore &&store) = delete;
};

class VerifastFrontendAction : public clang::ASTFrontendAction {
  Builder m_builder;
  AnnotationStore m_store;
  CommentProcessor m_commentProcessor;
  InclusionContext m_context;

public:
  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &compiler,
                    llvm::StringRef inFile) override {
    auto &PP = compiler.getPreprocessor();
    PP.addPPCallbacks(std::make_unique<ContextFreePPCallbacks>(
        m_context, PP, allowExpansions));
    PP.addCommentHandler(&m_commentProcessor);
    return std::make_unique<VerifastASTConsumer>(m_builder, m_store, m_context);
  }

  explicit VerifastFrontendAction(Builder &&builder)
      : m_builder(builder), m_commentProcessor(m_store) {}
};

using msg_builders = std::list<capnp::MallocMessageBuilder>;

class VerifastActionFactory : public clang::tooling::FrontendActionFactory {
  msg_builders &m_builders;

public:
  std::unique_ptr<clang::FrontendAction> create() override {
    m_builders.emplace_back();
    return std::make_unique<VerifastFrontendAction>(
        m_builders.back().initRoot<stubs::TU>());
  }

  explicit VerifastActionFactory(msg_builders &builders)
      : m_builders(builders) {}
  VerifastActionFactory(Builder &&builder) = delete;
};

} // namespace vf

int main(int argc, const char **argv) {
  auto expectedParser =
      clang::tooling::CommonOptionsParser::create(argc, argv, category);
  if (!expectedParser) {
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
