#include "ContextFreePPCallbacks.h"

namespace vf {

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
  if (undef && !m_context->currentInclusion().hasMacroDefinition(
                   MD, m_preprocessor->getSourceManager())) {
    reportUndefIsolatedMacro(macroNameTok, name, undef->getLocation());
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

void ContextFreePPCallbacks::MacroExpands(const clang::Token &macroNameTok,
                                          const clang::MacroDefinition &MD,
                                          clang::SourceRange range,
                                          const clang::MacroArgs *args) {
  std::string name(getMacroName(macroNameTok));
  if (macroAllowed(name))
    return;
  bool macroDefined = m_context->currentInclusion().hasMacroDefinition(
      MD, m_preprocessor->getSourceManager());
  if (!macroDefined) {
    reportCtxSensitiveMacroExpansion(macroNameTok, name, range.getBegin());
  }
}

void ContextFreePPCallbacks::FileChanged(
    clang::SourceLocation loc, FileChangeReason reason,
    clang::SrcMgr::CharacteristicKind fileType, clang::FileID prevFID) {
  switch (reason) {
  case EnterFile: {
    auto fileID = m_preprocessor->getSourceManager().getFileID(loc);
    auto includeLoc = m_preprocessor->getSourceManager().getIncludeLoc(fileID);
    // check if we entered an included file
    if (includeLoc.isValid()) {
      auto fileEntry =
          m_preprocessor->getSourceManager().getFileEntryForID(fileID);
      assert(fileEntry);
      m_context->startInclusionForFile(fileEntry);
    }
    break;
  }
  case ExitFile: {
    if (m_context->hasInclusions()) {
      const clang::FileEntry *exitedFileEntry =
          m_preprocessor->getSourceManager().getFileEntryForID(prevFID);
      if (exitedFileEntry &&
          exitedFileEntry->getUID() ==
              m_context->currentInclusion().getFileEntry()->getUID()) {
        m_context->endCurrentInclusion();
      }
    }
    break;
  }
  default:
    return;
  }
}

void ContextFreePPCallbacks::FileSkipped(
    const clang::FileEntryRef &skippedFile, const clang::Token &filenameTok,
    clang::SrcMgr::CharacteristicKind fileType) {
  const clang::FileEntry &fileEntry = skippedFile.getFileEntry();
  m_context->startInclusionForFile(&fileEntry);
  m_context->endCurrentInclusion();
}

void ContextFreePPCallbacks::InclusionDirective(
    clang::SourceLocation hashLoc, const clang::Token &includeTok,
    clang::StringRef fileName, bool isAngled,
    clang::CharSourceRange filenameRange, clang::OptionalFileEntryRef file,
    clang::StringRef searchPath, clang::StringRef relativePath,
    const clang::Module *imported, clang::SrcMgr::CharacteristicKind fileType) {
  if (file.has_value()) {
    m_context->currentInclusion().addIncludeDirective(
        {filenameRange.getAsRange(), fileName, file->getUID(), isAngled});
  }
}

void ContextFreePPCallbacks::reportMacroDivergence(
    const clang::Token &macroNameToken, std::string_view macroName) const {
  unsigned id = m_preprocessor->getDiagnostics().getCustomDiagID(
      clang::DiagnosticsEngine::Error, "Definition of '%0' has diverged");
  m_preprocessor->getDiagnostics().Report(macroNameToken.getLocation(), id)
      << macroName;
}

void ContextFreePPCallbacks::reportCtxSensitiveMacroExpansion(
    const clang::Token &macroNameToken, std::string_view macroName,
    clang::SourceLocation loc) const {
  unsigned id = m_preprocessor->getDiagnostics().getCustomDiagID(
      clang::DiagnosticsEngine::Error,
      "Macro expansion of '%0' is context sensitive");
  m_preprocessor->getDiagnostics().Report(loc, id) << macroName;
}

void ContextFreePPCallbacks::reportUndefIsolatedMacro(
    const clang::Token &macroNameToken, std::string_view macroName,
    clang::SourceLocation loc) const {
  unsigned id = m_preprocessor->getDiagnostics().getCustomDiagID(
      clang::DiagnosticsEngine::Error,
      "'#undef %0': no definition exists in the current context");
  m_preprocessor->getDiagnostics().Report(loc, id) << macroName;
}

void ContextFreePPCallbacks::checkDivergence(const clang::Token &macroNameToken,
                                             const clang::MacroDefinition &MD) {
  std::string name(getMacroName(macroNameToken));
  if (macroAllowed(name))
    return;
  bool hasLocalDef = m_context->currentInclusion().hasMacroDefinition(
      MD, m_preprocessor->getSourceManager());
  bool hasGlobalDef = MD.getMacroInfo();
  if (hasLocalDef ^ hasGlobalDef) {
    reportMacroDivergence(macroNameToken, name);
  }
}

std::string
ContextFreePPCallbacks::getMacroName(const clang::Token &macroNameToken) const {
  return m_preprocessor->getSpelling(macroNameToken);
}

bool ContextFreePPCallbacks::macroAllowed(std::string_view macroName) const {
  clang::StringRef n(macroName);
  return n.startswith("__VF_CXX_CLANG_FRONTEND__") ||
         m_macroWhiteList.contains(macroName);
}

} // namespace vf