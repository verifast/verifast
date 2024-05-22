#include "Inclusion.h"

namespace vf {

void Inclusion::addIncludeDirective(IncludeDirective includeDirective) {
  assert((m_includeDirectives.empty() ||
          m_includeDirectives.back().range.getEnd() <
              includeDirective.range.getBegin()) &&
         "Include directive in wrong order");
  m_includeDirectives.push_back(includeDirective);
}

void Inclusion::addInclusion(const Inclusion *inclusion) {
  assert(this != inclusion && "Inclusion cycle");
  m_inclusions.push_back(inclusion);
}

bool Inclusion::hasMacroDefinition(
    const clang::MacroDefinition &definition,
    const clang::SourceManager &sourceManager) const {
  // macro info is null when no definition exists
  if (const clang::MacroInfo *macroInfo = definition.getMacroInfo()) {
    clang::SourceLocation macroDefLoc = macroInfo->getDefinitionLoc();
    clang::FileID macroFileID = sourceManager.getFileID(macroDefLoc);
    if (const clang::FileEntry *macroFileEntry =
            sourceManager.getFileEntryForID(macroFileID)) {
      return includesFile(macroFileEntry);
    }
  }
  return false;
}

bool Inclusion::includesFile(const clang::FileEntry *fileEntry) const {
  if (m_fileEntry->getUID() == fileEntry->getUID()) {
    return true;
  }
  for (const Inclusion *inclusion : m_inclusions) {
    if (inclusion->includesFile(fileEntry)) {
      return true;
    }
  }
  return false;
}

llvm::ArrayRef<IncludeDirective> Inclusion::getIncludeDirectives() const {
  return m_includeDirectives;
}

size_t Inclusion::nbIncludeDirectives() const {
  return m_includeDirectives.size();
}

} // namespace vf