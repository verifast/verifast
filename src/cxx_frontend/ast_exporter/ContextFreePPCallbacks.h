#pragma once
#include "InclusionContext.h"
#include "clang/Lex/PPCallbacks.h"
#include "llvm/ADT/StringSet.h"

namespace vf {

/**
 * @brief Callbacks that are invoked during preprocessing.
 *
 */
class ContextFreePPCallbacks : public clang::PPCallbacks {
public:
  void MacroUndefined(const clang::Token &macroNameTok,
                      const clang::MacroDefinition &MD,
                      const clang::MacroDirective *undef) override;

  void Defined(const clang::Token &macroNameTok,
               const clang::MacroDefinition &MD,
               clang::SourceRange range) override;

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
                   clang::FileID prevFID) override;

  // Header guards: does not enter and afterwards exit the file when it is
  // skipped.
  void FileSkipped(const clang::FileEntryRef &skippedFile,
                   const clang::Token &filenameTok,
                   clang::SrcMgr::CharacteristicKind fileType) override;

  void InclusionDirective(clang::SourceLocation hashLoc,
                          const clang::Token &includeTok,
                          clang::StringRef fileName, bool isAngled,
                          clang::CharSourceRange filenameRange,
                          clang::OptionalFileEntryRef file,
                          clang::StringRef searchPath,
                          clang::StringRef relativePath,
                          const clang::Module *imported,
                          clang::SrcMgr::CharacteristicKind fileType) override;

  ContextFreePPCallbacks(InclusionContext &context,
                         const clang::Preprocessor &preprocessor,
                         llvm::ArrayRef<std::string> whiteList)
      : m_context(&context), m_preprocessor(&preprocessor) {
    for (auto s : whiteList) {
      m_macroWhiteList.insert(s);
    }
    auto mainEntry = m_preprocessor->getSourceManager().getFileEntryForID(
        m_preprocessor->getSourceManager().getMainFileID());
    m_context->startInclusionForFile(mainEntry);
  }

private:
  void reportMacroDivergence(const clang::Token &macroNameToken,
                             std::string_view macroName) const;

  void reportCtxSensitiveMacroExpansion(const clang::Token &macroNameToken,
                                        std::string_view macroName,
                                        clang::SourceLocation loc) const;

  void reportUndefIsolatedMacro(const clang::Token &macroNameToken,
                                std::string_view macroName,
                                clang::SourceLocation loc) const;

  void checkDivergence(const clang::Token &macroNameToken,
                       const clang::MacroDefinition &MD);

  std::string getMacroName(const clang::Token &macroNameToken) const;

  bool macroAllowed(std::string_view macroName) const;

  const clang::Preprocessor *m_preprocessor;
  llvm::StringSet<> m_macroWhiteList;
  InclusionContext *m_context;
};

} // namespace vf