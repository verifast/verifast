#include "ContextFreePPCallbacks.h"
#include "clang/Basic/FileManager.h"

namespace vf {

void ContextFreePPCallbacks::PPDiags::reportMacroDivergence(
    const clang::Token &macroNameTok, const std::string &macroName) {
  auto id = getDiagsEngine().getCustomDiagID(clang::DiagnosticsEngine::Error,
                                             "Definition of '%0' has diverged");
  getDiagsEngine().Report(macroNameTok.getLocation(), id) << macroName;
}

void ContextFreePPCallbacks::PPDiags::reportCtxSensitiveMacroExp(
    const clang::Token &macroNameTok, const std::string &macroName,
    clang::SourceLocation loc) {
  auto id = getDiagsEngine().getCustomDiagID(
      clang::DiagnosticsEngine::Error,
      "Macro expansion of '%0' is context sensitive");
  getDiagsEngine().Report(loc, id) << macroName;
}

void ContextFreePPCallbacks::PPDiags::reportUndefIsolatedMacro(
    const clang::Token &macroNameTok, const std::string &macroName,
    clang::SourceLocation loc) {
  auto id = getDiagsEngine().getCustomDiagID(
      clang::DiagnosticsEngine::Error,
      "'#undef %0': no definition exists in the current context");
  getDiagsEngine().Report(loc, id) << macroName;
}

std::string
ContextFreePPCallbacks::getMacroName(const clang::Token &macroNameToken) const {
  return m_PP.getSpelling(macroNameToken);
}

bool ContextFreePPCallbacks::macroAllowed(const std::string &macroName) const {
  clang::StringRef n(macroName);
  return n.startswith("__VF_CXX_CLANG_FRONTEND__") ||
         _whiteList.find(macroName) != _whiteList.end();
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
      m_context.startInclusion(*fileEntry);
    }
    break;
  }
  case ExitFile: {
    if (m_context.hasInclusions()) {
      auto exitedFileEntry = SM().getFileEntryForID(prevFID);
      if (exitedFileEntry &&
          exitedFileEntry->getUID() == m_context.currentInclusion()->getUID()) {
        m_context.endInclusion();
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
  auto name = getMacroName(macroNameTok);
  if (macroAllowed(name))
    return;
  if (undef && !m_context.currentInclusion()->ownsMacroDef(MD, SM())) {
    m_diags.reportUndefIsolatedMacro(macroNameTok, name, undef->getLocation());
  }
}

void ContextFreePPCallbacks::MacroExpands(const clang::Token &macroNameTok,
                                          const clang::MacroDefinition &MD,
                                          clang::SourceRange range,
                                          const clang::MacroArgs *args) {
  auto name = getMacroName(macroNameTok);
  if (macroAllowed(name))
    return;
  bool macroDefined = m_context.currentInclusion()->ownsMacroDef(MD, SM());
  if (!macroDefined) {
    m_diags.reportCtxSensitiveMacroExp(macroNameTok, name, range.getBegin());
  }
}

void ContextFreePPCallbacks::FileSkipped(
    const clang::FileEntryRef &skippedFile, const clang::Token &filenameTok,
    clang::SrcMgr::CharacteristicKind fileType) {
  auto &fileEntry = skippedFile.getFileEntry();
  m_context.startInclusion(fileEntry);
  m_context.endInclusion();
}

void ContextFreePPCallbacks::InclusionDirective(
    clang::SourceLocation hashLoc, const clang::Token &includeTok,
    clang::StringRef fileName, bool isAngled,
    clang::CharSourceRange filenameRange, clang::OptionalFileEntryRef file,
    clang::StringRef searchPath, clang::StringRef relativePath,
    const clang::Module *imported, clang::SrcMgr::CharacteristicKind fileType) {
  m_context.addRealInclDirective(filenameRange.getAsRange(), fileName, *file,
                                 isAngled);
}

void ContextFreePPCallbacks::checkDivergence(const clang::Token &macroNameTok,
                                             const clang::MacroDefinition &MD) {
  auto name = getMacroName(macroNameTok);
  if (macroAllowed(name))
    return;
  bool hasLocalDef = m_context.currentInclusion()->ownsMacroDef(MD, SM());
  bool hasGlobalDef = MD.getMacroInfo();
  if (hasLocalDef ^ hasGlobalDef) {
    m_diags.reportMacroDivergence(macroNameTok, name);
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