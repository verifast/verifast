#pragma once

#include "Serializer.h"
#include "stubs_ast.capnp.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/SourceLocation.h"
#include <string>

namespace vf {

/**
 * @brief Serializer and consumer of diagnostics. Saves all diagnostics that
 * were emitted while traversing the AST during serialization.
 *
 */
class DiagnosticSerializer : public Serializer<ListBuilder<stubs::Error>>,
                             public clang::DiagnosticConsumer {
public:
  clang::DiagnosticsEngine::Level getMinLevel() const { return m_minLevel; }

  virtual bool IncludeInDiagnosticCounts() const override { return true; }

  void BeginSourceFile(const clang::LangOptions &langOpts,
                       const clang::Preprocessor *preprocessor) override;

  void EndSourceFile() override;

  void HandleDiagnostic(clang::DiagnosticsEngine::Level level,
                        const clang::Diagnostic &info) override;

  size_t nbDiags() const { return m_diags.size(); }

  /**
   * @brief Serialize all diagnostics that are stored in this instance.
   *
   * @param builder Target builder to serialize to.
   */
  void serialize(ListBuilder<stubs::Error> builder) const override;

  DiagnosticSerializer(clang::DiagnosticsEngine::Level minLevel)
      : m_minLevel(minLevel) {}

private:
  /**
   * @brief Wrapper to save diagnostic information.
   *
   */
  struct Diag {
    clang::SourceLocation loc;
    std::string reason;
    const clang::SourceManager *sourceManager;
    const clang::LangOptions *langOpts;

    void serialize(stubs::Error::Builder builder) const;

    Diag(clang::SourceLocation loc, std::string_view reason,
         const clang::SourceManager &sourceManager,
         const clang::LangOptions *langOpts)
        : loc(loc), reason(reason), sourceManager(&sourceManager),
          langOpts(langOpts) {}
  };

  clang::DiagnosticsEngine::Level m_minLevel;
  const clang::LangOptions *m_langOpts;
  llvm::SmallVector<Diag> m_diags;
};

} // namespace vf