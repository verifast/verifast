#pragma once
#include "Context.h"
#include "kj/common.h"
#include "clang/Lex/PPCallbacks.h"
#include <unordered_set>

namespace vf {

class ContextFreePPCallbacks : public clang::PPCallbacks {

  class PPDiags {
    clang::Preprocessor &_PP;

    template <unsigned N>
    clang::DiagnosticBuilder createDiag(clang::SourceLocation loc,
                                        clang::DiagnosticsEngine::Level level,
                                        const char (&msg)[N]) const {
      auto id = _PP.getDiagnostics().getCustomDiagID(level, msg);
      return _PP.getDiagnostics().Report(loc, id);
    }

  public:
    explicit PPDiags(clang::Preprocessor &PP) : _PP(PP) {}

    void reportMacroDivergence(const clang::Token &macroNameTok,
                               const clang::MacroDefinition &MD);

    void reportCtxSensitiveMacroExp(const clang::Token &macroNameTok,
                                    const clang::MacroDefinition &MD,
                                    const clang::SourceRange &range);

    void reportUndefIsolatedMacro(const clang::Token &macroNameTok,
                                  const clang::MacroDefinition &MD);
  };

  Context &_context;
  clang::Preprocessor &_PP;
  const std::unordered_set<std::string> _whiteList;
  PPDiags _diags;

  const clang::SourceManager &SM() const { return _PP.getSourceManager(); }

  void checkDivergence(const clang::Token &macroNameToken,
                       const clang::MacroDefinition &MD);

public:
  explicit ContextFreePPCallbacks(Context &context, clang::Preprocessor &PP,
                                  const std::vector<std::string> &whiteList)
      : _context(context), _PP(PP), _whiteList(whiteList.begin(), whiteList.end()), _diags(PP) {
    auto mainEntry = SM().getFileEntryForID(SM().getMainFileID());
    _context.startInclusion(*mainEntry);
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
                          const clang::FileEntry *File,
                          clang::StringRef SearchPath,
                          clang::StringRef RelativePath,
                          const clang::Module *Imported,
                          clang::SrcMgr::CharacteristicKind FileType) override;
};
} // namespace vf