#include "Inclusion.h"
#include "AstSerializer.h"
#include "InclusionContext.h"
#include "Util.h"
#include "llvm/ADT/STLExtras.h"
#include <vector>

namespace vf {

static struct Comparator {
  bool operator()(const IncludeDirective &first,
                  const IncludeDirective &second) const {
    return first.getRange().getBegin() < second.getRange().getBegin();
  }
} comparator;

void RealIncludeDirective::serialize(stubs::Include::Builder &builder,
                                     const clang::SourceManager &SM,
                                     AstSerializer &serializer,
                                     const InclusionContext &context) const {
  auto realInclude = builder.initRealInclude();
  realInclude.setFd(m_fileUID);
  realInclude.setFileName(m_fileName.str());
  realInclude.setIsAngled(m_isAngled);

  auto locBuilder = realInclude.initLoc();
  serializeSrcRange(locBuilder, m_range, SM);

  auto &inclusion = context.getInclusionForFD(m_fileUID);
  std::vector<std::reference_wrapper<const IncludeDirective>>
      nestedIncludeDirectives;
  inclusion.sortIncludeDirectivesTo(nestedIncludeDirectives);

  serializer.validateIncludesBeforeFirstDecl(m_fileUID,
                                             nestedIncludeDirectives);

  auto nestedBuilders =
      realInclude.initIncludes(nestedIncludeDirectives.size());

  for (size_t i(0); i < nestedIncludeDirectives.size(); ++i) {
    auto nestedBuilder = nestedBuilders[i];
    const IncludeDirective &nestedInclude = nestedIncludeDirectives[i];
    nestedInclude.serialize(nestedBuilder, SM, serializer, context);
  }
}

void GhostIncludeDirective::serialize(stubs::Include::Builder &builder,
                                      const clang::SourceManager &SM,
                                      AstSerializer &serializer,
                                      const InclusionContext &context) const {
  auto ghostInclude = builder.initGhostInclude();
  serializer.serializeAnnotationClause(ghostInclude, *this);
}

bool Inclusion::containsInclusionFile(const clang::FileEntry &fileEntry) const {
  if (m_fileUID == fileEntry.getUID()) {
    return true;
  }
  for (auto incl : m_inclusions) {
    if (incl->containsInclusionFile(fileEntry)) {
      return true;
    }
  }
  return false;
}

bool Inclusion::ownsMacroDef(const clang::MacroDefinition &macroDef,
                             const clang::SourceManager &SM) const {
  // macro info is null when no definition exists
  if (auto *macroInfo = macroDef.getMacroInfo()) {
    auto macroDefLoc = macroInfo->getDefinitionLoc();
    auto macroFileID = SM.getFileID(macroDefLoc);
    if (auto *macroFileEntry = SM.getFileEntryForID(macroFileID)) {
      return containsInclusionFile(*macroFileEntry);
    }
  }
  return false;
}

void Inclusion::sortIncludeDirectivesTo(
    std::vector<std::reference_wrapper<const IncludeDirective>> &container)
    const {
  for (auto &directive : m_inclDirectives) {
    container.emplace_back(*directive);
  }
  llvm::sort(container.begin(), container.end(), comparator);
}

void Inclusion::serializeIncludeDirectives(
    capnp::List<stubs::Include, capnp::Kind::STRUCT>::Builder &builder,
    const clang::SourceManager &SM, AstSerializer &serializer,
    const InclusionContext &context) const {
  std::vector<std::reference_wrapper<const IncludeDirective>> includes;
  sortIncludeDirectivesTo(includes);

  serializer.validateIncludesBeforeFirstDecl(m_fileUID, includes);

  for (size_t i(0); i < includes.size(); ++i) {
    auto includeBuilder = builder[i];
    const IncludeDirective &include = includes[i];
    include.serialize(includeBuilder, SM, serializer, context);
  }
}

} // namespace vf