#include "InclusionSerializer.h"

namespace vf {

namespace {

struct Directive {
  virtual ~Directive() = default;

  virtual clang::SourceRange getRange() const = 0;

  virtual void
  serialize(stubs::Include::Builder builder,
            const InclusionSerializer &inclusionSerializer) const = 0;
};

struct RealDirective : public Directive, public IncludeDirective {
  clang::SourceRange getRange() const override { return range; }

  void
  serialize(stubs::Include::Builder builder,
            const InclusionSerializer &inclusionSerializer) const override {
    stubs::Include::RealInclude::Builder includeBuilder =
        builder.initRealInclude();

    includeBuilder.setFd(fileUID);
    includeBuilder.setFileName(fileName);
    includeBuilder.setIsAngled(isAngled);
    inclusionSerializer.getASTSerializer().serialize(includeBuilder.initLoc(),
                                                     range);

    const Inclusion &inclusionOfDirective =
        inclusionSerializer.getInclusionContext().getInclusionOfFileUID(
            fileUID);

    ListBuilder<stubs::Include> includesBuilder = includeBuilder.initIncludes(
        inclusionOfDirective.nbIncludeDirectives() +
        inclusionSerializer.getASTSerializer()
            .getAnnotationManager()
            .getLeadingIncludes(inclusionOfDirective.getFileEntry())
            .size());

    inclusionSerializer.serialize(inclusionOfDirective, includesBuilder);
  }

  RealDirective(const IncludeDirective &directive)
      : IncludeDirective(directive) {}
};

struct GhostDirective : public Directive, public Annotation {
  clang::SourceRange getRange() const override {
    return Annotation::getRange();
  }

  void
  serialize(stubs::Include::Builder builder,
            const InclusionSerializer &inclusionSerializer) const override {
    inclusionSerializer.getASTSerializer().serialize(builder.initGhostInclude(),
                                                     *this);
  }

  GhostDirective(const Annotation &directive) : Annotation(directive) {}
};

void getDirectives(
    const Inclusion &inclusion, const AnnotationManager &annotationManager,
    llvm::SmallVectorImpl<std::unique_ptr<Directive>> &directives) {
  llvm::ArrayRef<IncludeDirective> realDirectives =
      inclusion.getIncludeDirectives();
  AnnotationsRef ghostDirectives =
      annotationManager.getLeadingIncludes(inclusion.getFileEntry());

  directives.clear();
  directives.reserve(realDirectives.size() + ghostDirectives.size());
  for (const IncludeDirective &directive : realDirectives) {
    directives.emplace_back(std::make_unique<RealDirective>(directive));
  }
  for (const Annotation &directive : ghostDirectives) {
    directives.emplace_back(std::make_unique<GhostDirective>(directive));
  }

  llvm::sort(directives, [](const std::unique_ptr<Directive> &d1,
                            const std::unique_ptr<Directive> &d2) {
    return d1->getRange().getBegin() < d2->getRange().getBegin();
  });
}

} // namespace

clang::SourceLocation InclusionSerializer::getFirstDeclLocInFile(
    const clang::FileEntry *fileEntry) const {
  auto it = m_firstDeclLocMap->find(fileEntry->getUID());
  if (it == m_firstDeclLocMap->end()) {
    return {};
  }
  return it->getSecond();
}

void InclusionSerializer::serialize(const Inclusion &inclusion,
                                    ListBuilder<stubs::Include> builder) const {
  llvm::SmallVector<std::unique_ptr<Directive>> directives;
  getDirectives(inclusion, m_serializer->getAnnotationManager(), directives);

  assert(directives.size() == builder.size() &&
         "Target builder has wrong size");

  std::optional<clang::SourceLocation> lastDirectiveLoc =
      directives.empty() ? clang::SourceLocation()
                         : directives.back()->getRange().getBegin();
  std::optional<clang::SourceLocation> firstDeclLoc =
      getFirstDeclLocInFile(inclusion.getFileEntry());

  if (firstDeclLoc.has_value() && firstDeclLoc->isValid() &&
      lastDirectiveLoc.has_value() && lastDirectiveLoc->isValid() &&
      *firstDeclLoc < *lastDirectiveLoc) {
    clang::DiagnosticsEngine &diagsEngine =
        m_serializer->getASTContext().getDiagnostics();
    unsigned diagID = diagsEngine.getCustomDiagID(
        clang::DiagnosticsEngine::Error,
        "'#include' directive cannot appear after a declaration");
    diagsEngine.Report(*lastDirectiveLoc, diagID);
  }

  size_t i(0);
  for (const std::unique_ptr<Directive> &directive : directives) {
    directive->serialize(builder[i++], *this);
  }
}

} // namespace vf