#include "Annotation.h"
#include "AstSerializer.h"
#include "CommentProcessor.h"
#include "ContextFreePPCallbacks.h"
#include "DiagnosticCollectorConsumer.h"
#include "Inclusion.h"
#include "Location.h"
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

class VerifastASTConsumer : public clang::ASTConsumer {
  stubs::TU::Builder m_builder;
  AnnotationStore &m_store;
  InclusionContext &m_context;

public:
  void HandleTranslationUnit(clang::ASTContext &context) override {
    AstSerializer serializer(
        context, m_store, m_context,
        capnp::Orphanage::getForMessageContaining(m_builder),
        exportImplicitDecls);
    serializer.serializeTU(m_builder, context.getTranslationUnitDecl());
  }

  explicit VerifastASTConsumer(stubs::TU::Builder builder,
                               AnnotationStore &store,
                               InclusionContext &context)
      : m_builder(builder), m_store(store), m_context(context) {}
};

class VerifastFrontendAction : public clang::ASTFrontendAction {
  stubs::TU::Builder m_builder;
  AnnotationStore m_store;
  CommentProcessor m_commentProcessor;
  InclusionContext m_context;
  DiagnosticCollectorConsumer &m_diags;

public:
  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &compiler,
                    llvm::StringRef inFile) override {
    auto &PP = compiler.getPreprocessor();
    PP.addPPCallbacks(std::make_unique<ContextFreePPCallbacks>(
        m_context, PP, allowExpansions));
    PP.addCommentHandler(&m_commentProcessor);
    compiler.getDiagnostics().setClient(&m_diags, false);
    return std::make_unique<VerifastASTConsumer>(m_builder, m_store, m_context);
  }

  explicit VerifastFrontendAction(stubs::TU::Builder builder,
                                  DiagnosticCollectorConsumer &diags)
      : m_builder(builder), m_commentProcessor(m_store), m_diags(diags) {}
};

class VerifastActionFactory : public clang::tooling::FrontendActionFactory {
  stubs::TU::Builder m_builder;

public:
  DiagnosticCollectorConsumer diags;

  std::unique_ptr<clang::FrontendAction> create() override {
    return std::make_unique<VerifastFrontendAction>(m_builder, diags);
  }

  explicit VerifastActionFactory(stubs::SerResult::Builder builder)
      : m_builder(builder.initTu()),
        diags(clang::DiagnosticsEngine::Level::Error) {}
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
  capnp::MallocMessageBuilder messageBuilder;
  auto serResultBuilder = messageBuilder.initRoot<stubs::SerResult>();

  vf::VerifastActionFactory factory(serResultBuilder);

  auto error = tool.run(&factory);

  auto errors = factory.diags.getErrors();
  if (errors.size() > 0) {
    auto errorsBuilder = serResultBuilder.initErrors(errors.size());
    size_t i(0);
    for (; i < errors.size(); ++i) {
      auto &error = errors[i];
      auto errorBuilder = errorsBuilder[i];
      error.serialize(errorBuilder);
    }
  }

  capnp::writeMessageToFd(1, messageBuilder);

  return error;
}
