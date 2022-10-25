#include "InclusionContext.h"

namespace vf {
void InclusionContext::serializeInclDirectivesCore(
    capnp::List<stubs::Include, capnp::Kind::STRUCT>::Builder &builder,
    const clang::SourceManager &SM,
    const llvm::ArrayRef<InclDirective> inclDirectives,
    get_first_decl_loc_fn &getFirstDeclLocOpt, unsigned fd) const {
  if (inclDirectives.size() > 0) {
    auto &lastInclDir = inclDirectives.back();
    auto firstDeclLocOpt = getFirstDeclLocOpt(fd);
    if (firstDeclLocOpt &&
        lastInclDir.m_range.getEnd() > firstDeclLocOpt.getValue()) {
      auto diagID = SM.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Level::Error,
          "An include directive can only appear at the start of a file.");
      SM.getDiagnostics().Report(lastInclDir.m_range.getBegin(), diagID);
    }
  }

  for (size_t i(0); i < inclDirectives.size(); ++i) {
    auto inclDirBuilder = builder[i];
    auto inclDirective = inclDirectives[i];
    auto currentFd = inclDirective.m_fileUID;

    inclDirBuilder.setFd(currentFd);
    inclDirBuilder.setFileName(inclDirective.m_fileName.str());
    inclDirBuilder.setIsAngled(inclDirective.m_isAngled);
    auto locBuilder = inclDirBuilder.initLoc();
    serializeSrcRange(locBuilder, inclDirective.m_range, SM);

    auto &nestedInclDirectives = m_includesMap.at(currentFd).getInclDirectives();
    auto nestedInclDirectivesBuilder =
        inclDirBuilder.initIncludes(nestedInclDirectives.size());
    serializeInclDirectivesCore(nestedInclDirectivesBuilder, SM,
                                nestedInclDirectives, getFirstDeclLocOpt,
                                currentFd);
  }
}

void InclusionContext::serializeTUInclDirectives(
    stubs::TU::Builder &builder, const clang::SourceManager &SM,
    get_first_decl_loc_fn &getFirstDeclLocOpt) const {
  auto mainUID = SM.getFileEntryForID(SM.getMainFileID())->getUID();
  auto &inclDirectives = m_includesMap.at(mainUID).getInclDirectives();
  auto inclDirectivesBuilder = builder.initIncludes(inclDirectives.size());
  serializeInclDirectivesCore(inclDirectivesBuilder, SM, inclDirectives,
                              getFirstDeclLocOpt, mainUID);
}
} // namespace vf