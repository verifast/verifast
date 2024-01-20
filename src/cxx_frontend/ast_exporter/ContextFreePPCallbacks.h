#pragma once
#include "Inclusion.h"
#include "kj/common.h"
#include "clang/Lex/PPCallbacks.h"
#include <unordered_set>

namespace vf {

class ContextFreePPCallbacks : public clang::PPCallbacks {

  class PPDiags {
    clang::Preprocessor &m_PP;

    clang::DiagnosticsEngine &getDiagsEngine() const {
      return m_PP.getDiagnostics();
    }

  public:
    explicit PPDiags(clang::Preprocessor &PP) : m_PP(PP) {}

    void reportMacroDivergence(const clang::Token &macroNameTok,
                               const std::string &macroName);

    void reportCtxSensitiveMacroExp(const clang::Token &macroNameTok,
                                    const std::string &macroName,
                                    clang::SourceLocation loc);

    void reportUndefIsolatedMacro(const clang::Token &macroNameTok,
                                  const std::string &macroName,
                                  clang::SourceLocation loc);
  };

  InclusionContext &m_context;
  clang::Preprocessor &m_PP;
  const std::unordered_set<std::string> _whiteList;
  PPDiags m_diags;

  const clang::SourceManager &SM() const { return m_PP.getSourceManager(); }

  void checkDivergence(const clang::Token &macroNameToken,
                       const clang::MacroDefinition &MD);

  std::string getMacroName(const clang::Token &macroNameToken) const;

  bool macroAllowed(const std::string &macroName) const;

public:
  explicit ContextFreePPCallbacks(InclusionContext &context,
                                  clang::Preprocessor &PP,
                                  const std::vector<std::string> &whiteList)
      : m_context(context), m_PP(PP),
        _whiteList(whiteList.begin(), whiteList.end()), m_diags(PP) {
    auto mainEntry = SM().getFileEntryForID(SM().getMainFileID());
    m_context.startInclusion(*mainEntry);
  }

  KJ_DISALLOW_COPY(ContextFreePPCallbacks);

  void MacroUndefined(const clang::Token &macroNameTok,
                      const clang::MacroDefinition &MD,
                      const clang::MacroDirective *undef) override;

  void Defined(const clang::Token &MacroNameTok,
               const clang::MacroDefinition &MD,
               clang::SourceRange Range) override;

  void Ifdef(clang::SourceLocation loc, const clang::Token &macroNameTok,
             const clang::MacroDefinition &MD) override;

  void Ifndef(clang::SourceLocation loc, const clang::Token &macroNameTok,
              const clang::MacroDefinition &MD) override;

  void MacroExpands(const clang::Token &macroNameTok,
                    const clang::MacroDefinition &MD, clang::SourceRange range,
                    const clang::MacroArgs *args) override;

  // EnterFile is not called when a file is skipped due to header guards.
  void FileChanged(clang::SourceLocation loc, FileChangeReason reason,
                   clang::SrcMgr::CharacteristicKind fileType,
                   clang::FileID prevFID = clang::FileID()) override;

  // Header guards: does not enter and afterwards exit the file when it is
  // skipped.
  void FileSkipped(const clang::FileEntryRef &skippedFile,
                   const clang::Token &filenameTok,
                   clang::SrcMgr::CharacteristicKind fileType) override;

  void InclusionDirective(clang::SourceLocation HashLoc,
                          const clang::Token &IncludeTok,
                          clang::StringRef FileName, bool IsAngled,
                          clang::CharSourceRange FilenameRange,
                          clang::OptionalFileEntryRef File,
                          clang::StringRef SearchPath,
                          clang::StringRef RelativePath,
                          const clang::Module *Imported,
                          clang::SrcMgr::CharacteristicKind FileType) override;
};
} // namespace vf