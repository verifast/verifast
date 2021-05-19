#include "Context.h"

namespace vf {
void Context::serializeInclDirectivesCore(
    capnp::List<stubs::Include, capnp::Kind::STRUCT>::Builder &builder,
    const clang::SourceManager &SM,
    const llvm::ArrayRef<InclDirective> inclDirectives,
    get_first_decl_loc_fn &getFirstDeclLocOpt, unsigned fd) const {
  if (inclDirectives.size() > 0) {
    auto &lastInclDir = inclDirectives.back();
    auto firstDeclLocOpt = getFirstDeclLocOpt(fd);
    if (firstDeclLocOpt &&
        lastInclDir._range.getEnd() > firstDeclLocOpt.getValue()) {
      auto diagID = SM.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Level::Error,
          "An include directive can only appear at the start of a file.");
      SM.getDiagnostics().Report(lastInclDir._range.getBegin(), diagID);
    }
  }

  for (size_t i(0); i < inclDirectives.size(); ++i) {
    auto inclDirBuilder = builder[i];
    auto inclDirective = inclDirectives[i];
    auto currentFd = inclDirective._fileUID;

    inclDirBuilder.setFd(currentFd);
    inclDirBuilder.setFileName(inclDirective._fileName.str());
    inclDirBuilder.setIsAngled(inclDirective._isAngled);
    auto locBuilder = inclDirBuilder.initLoc();
    serializeSrcRange(locBuilder, inclDirective._range, SM);

    auto &nestedInclDirectives = _includesMap.at(currentFd).getInclDirectives();
    auto nestedInclDirectivesBuilder =
        inclDirBuilder.initIncludes(nestedInclDirectives.size());
    serializeInclDirectivesCore(nestedInclDirectivesBuilder, SM,
                                nestedInclDirectives, getFirstDeclLocOpt,
                                currentFd);
  }
}

void Context::serializeTUInclDirectives(
    stubs::TU::Builder &builder, const clang::SourceManager &SM,
    get_first_decl_loc_fn &getFirstDeclLocOpt) const {
  auto mainUID = SM.getFileEntryForID(SM.getMainFileID())->getUID();
  auto &inclDirectives = _includesMap.at(mainUID).getInclDirectives();
  auto inclDirectivesBuilder = builder.initIncludes(inclDirectives.size());
  serializeInclDirectivesCore(inclDirectivesBuilder, SM, inclDirectives,
                              getFirstDeclLocOpt, mainUID);
}
} // namespace vf