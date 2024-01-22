#include "Inclusion.h"

namespace vf {

void InclusionContext::startInclusion(const clang::FileEntry &fileEntry) {
  auto it = m_includesMap.emplace(fileEntry.getUID(), fileEntry);
  auto &startedIncl = it.first->second;
  m_includesStack.push_back(&startedIncl);
  // TODO: what if we start an inclusion that we already processed? -> does
  // not have header guards; then it.second will be false
}

void InclusionContext::endInclusion() {
  auto ended = currentInclusion();
  m_includesStack.pop_back();
  currentInclusion()->addInclusion(ended);
}

void InclusionContext::serializeTUInclDirectives(
    stubs::TU::Builder &builder, const clang::SourceManager &SM,
    AstSerializer &serializer) const {
  auto mainUID = SM.getFileEntryForID(SM.getMainFileID())->getUID();
  auto &inclusion = m_includesMap.at(mainUID);
  auto includesBuilder =
      builder.initIncludes(inclusion.getNbIncludeDirectives());
  inclusion.serializeIncludeDirectives(includesBuilder, SM, serializer, *this);
}
} // namespace vf