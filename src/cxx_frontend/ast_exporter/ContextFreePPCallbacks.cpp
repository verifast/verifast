#include "ContextFreePPCallbacks.h"
#include "clang/Basic/FileManager.h"

namespace vf {

void ContextFreePPCallbacks::PPDiags::reportMacroDivergence(
    const clang::Token &macroNameTok, const clang::MacroDefinition &MD) {
  auto tokenSpelling = _PP.getSpelling(macroNameTok);
  auto loc = macroNameTok.getLocation();
  auto globalDef = MD.getMacroInfo();
  createDiag(loc, clang::DiagnosticsEngine::Level::Error,
             "Definition of '%0' has diverged. Its definition is%1 defined in "
             "the current context, while%2 defined in the parent context.")
      << tokenSpelling << (globalDef ? " not" : "")
      << (globalDef ? "" : " not");
}

void ContextFreePPCallbacks::PPDiags::reportCtxSensitiveMacroExp(
    const clang::Token &macroNameTok, const clang::MacroDefinition &MD,
    const clang::SourceRange &range) {
  createDiag(range.getBegin(), clang::DiagnosticsEngine::Level::Error,
             "Macro expansion of '%0' is context sensitive. Last definition is "
             "here: %1")
      << _PP.getSpelling(macroNameTok)
      << MD.getMacroInfo()->getDefinitionLoc().printToString(
             _PP.getSourceManager());
}

void ContextFreePPCallbacks::PPDiags::reportUndefIsolatedMacro(
    const clang::Token &macroNameTok, const clang::MacroDefinition &MD) {
  createDiag(macroNameTok.getLocation(), clang::DiagnosticsEngine::Level::Error,
             "'Undefining '%0', which has no definition in the current "
             "context. Last definition is here: %1")
      << _PP.getSpelling(macroNameTok)
      << MD.getMacroInfo()->getDefinitionLoc().printToString(
             _PP.getSourceManager());
}

void ContextFreePPCallbacks::FileChanged(
    clang::SourceLocation loc, FileChangeReason reason,
    clang::SrcMgr::CharacteristicKind fileType, clang::FileID prevFID) {
  switch (reason) {
  case EnterFile: {
    auto fileID = SM().getFileID(loc);
    auto includeLoc = SM().getIncludeLoc(fileID);
    // check if we entered an included file
    if (includeLoc.isValid()) {
      auto fileEntry = SM().getFileEntryForID(fileID);
      assert(fileEntry);
      _context.startInclusion(*fileEntry);
    }
    break;
  }
  case ExitFile: {
    if (_context.hasInclusions()) {
      auto exitedFileEntry = SM().getFileEntryForID(prevFID);
      if (exitedFileEntry &&
          exitedFileEntry->getUID() == _context.currentInclusion()->fileUID) {
        _context.endInclusion();
      }
    }
    break;
  }
  default:
    return;
  }
}

void ContextFreePPCallbacks::MacroUndefined(
    const clang::Token &macroNameTok, const clang::MacroDefinition &MD,
    const clang::MacroDirective *undef) {
  // C++ allows to undef a macro that has not been defined, so we could
  // allow it, but it may be better to raise an error to be more compliant with
  // the context-free awareness.

  // We allow to undef a macro that is defined in the current context.
  // It is not allowed to undef a macro that is globally defined, but not in the
  // current context. We still allow to undef macro's that haven't been defined
  // at all.
  if (undef && !_context.currentInclusion()->ownsMacroDef(MD, SM())) {
    _diags.reportUndefIsolatedMacro(macroNameTok, MD);
  }
}

void ContextFreePPCallbacks::MacroExpands(const clang::Token &macroNameTok,
                                          const clang::MacroDefinition &MD,
                                          clang::SourceRange range,
                                          const clang::MacroArgs *args) {
  if (_whiteList.find(_PP.getSpelling(macroNameTok)) == _whiteList.end()) {
    bool macroDefined = _context.currentInclusion()->ownsMacroDef(MD, SM());
    if (!macroDefined) {
      _diags.reportCtxSensitiveMacroExp(macroNameTok, MD, range);
    }
  }
}

void ContextFreePPCallbacks::FileSkipped(
    const clang::FileEntryRef &skippedFile, const clang::Token &filenameTok,
    clang::SrcMgr::CharacteristicKind fileType) {
  auto &fileEntry = skippedFile.getFileEntry();
  _context.startInclusion(fileEntry);
  _context.endInclusion();
}

void ContextFreePPCallbacks::InclusionDirective(
    clang::SourceLocation hashLoc, const clang::Token &includeTok,
    clang::StringRef fileName, bool isAngled,
    clang::CharSourceRange filenameRange, const clang::FileEntry *file,
    clang::StringRef searchPath, clang::StringRef relativePath,
    const clang::Module *imported, clang::SrcMgr::CharacteristicKind fileType) {
  _context.addInclDirective(filenameRange.getAsRange(), fileName, *file, isAngled);
}

void ContextFreePPCallbacks::checkDivergence(const clang::Token &macroNameTok,
                                             const clang::MacroDefinition &MD) {
  bool hasLocalDef = _context.currentInclusion()->ownsMacroDef(MD, SM());
  bool hasGlobalDef = MD.getMacroInfo();
  if (hasLocalDef ^ hasGlobalDef) {
    _diags.reportMacroDivergence(macroNameTok, MD);
  }
}

void ContextFreePPCallbacks::Defined(const clang::Token &macroNameTok,
                                     const clang::MacroDefinition &MD,
                                     clang::SourceRange range) {
  checkDivergence(macroNameTok, MD);
}

void ContextFreePPCallbacks::Ifdef(clang::SourceLocation loc,
                                   const clang::Token &macroNameTok,
                                   const clang::MacroDefinition &MD) {
  checkDivergence(macroNameTok, MD);
}

void ContextFreePPCallbacks::Ifndef(clang::SourceLocation loc,
                                    const clang::Token &macroNameTok,
                                    const clang::MacroDefinition &MD) {
  checkDivergence(macroNameTok, MD);
}

} // namespace vf