#include "AnnotationManager.h"
#include "CommentProcessor.h"
#include "ContextFreePPCallbacks.h"
#include "DiagnosticSerializer.h"
#include "InclusionContext.h"
#include "TranslationUnitSerializer.h"
#include "capnp/message.h"
#include "capnp/serialize.h"
#include "stubs_ast.capnp.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"

#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif

namespace {

static llvm::cl::OptionCategory category("VeriFast AST exporter options");

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

} // namespace

namespace vf {

class VeriFastASTConsumer : public clang::ASTConsumer {
public:
  void HandleTranslationUnit(clang::ASTContext &context) override {
    capnp::MallocMessageBuilder messageBuilder;
    stubs::SerResult::Builder resultBuilder =
        messageBuilder.initRoot<stubs::SerResult>();

    TranslationUnitSerializer serializer(
        context, *m_annotationManager, *m_inclusionContext,
        messageBuilder.getOrphanage(), !exportImplicitDecls);

    serializer.serialize(context.getTranslationUnitDecl(),
                         resultBuilder.initTu());

    if (m_diags->nbDiags() > 0) {
      m_diags->serialize(resultBuilder.initErrors(m_diags->nbDiags()));
    }

    capnp::writeMessageToFd(1, messageBuilder);
  }

  VeriFastASTConsumer(const DiagnosticSerializer &diags,
                      const AnnotationManager &annotationManager,
                      const InclusionContext &inclusionContext)
      : m_diags(&diags), m_annotationManager(&annotationManager),
        m_inclusionContext(&inclusionContext) {}

private:
  const DiagnosticSerializer *m_diags;
  const AnnotationManager *m_annotationManager;
  const InclusionContext *m_inclusionContext;
};

class VeriFastFrontendAction : public clang::ASTFrontendAction {
public:
  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &compiler,
                    llvm::StringRef inFile) override {
    m_annotationManager = std::make_unique<AnnotationManager>(
        compiler.getSourceManager(), compiler.getLangOpts());
    m_commentProcessor =
        std::make_unique<CommentProcessor>(*m_annotationManager);

    compiler.getDiagnostics().setClient(&m_diags, false);
    compiler.getPreprocessor().addCommentHandler(m_commentProcessor.get());
    compiler.getPreprocessor().addPPCallbacks(
        std::make_unique<ContextFreePPCallbacks>(
            m_inclusionContext, compiler.getPreprocessor(), allowExpansions));

    return std::make_unique<VeriFastASTConsumer>(m_diags, *m_annotationManager,
                                                 m_inclusionContext);
  }

  explicit VeriFastFrontendAction()
      : m_diags(clang::DiagnosticsEngine::Error) {}

private:
  DiagnosticSerializer m_diags;
  std::unique_ptr<AnnotationManager> m_annotationManager;
  std::unique_ptr<CommentProcessor> m_commentProcessor;
  InclusionContext m_inclusionContext;
};

class VeriFastActionFactory : public clang::tooling::FrontendActionFactory {
public:
  std::unique_ptr<clang::FrontendAction> create() override {
    return std::make_unique<VeriFastFrontendAction>();
  }
};

} // namespace vf

int main(int argc, const char **argv) {
  llvm::Expected<clang::tooling::CommonOptionsParser> expectedParser =
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

  vf::VeriFastActionFactory factory;
  int error = tool.run(&factory);

  return error;
}