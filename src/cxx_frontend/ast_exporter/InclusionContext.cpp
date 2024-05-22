#include "InclusionContext.h"

namespace vf {
void InclusionContext::startInclusionForFile(
    const clang::FileEntry *fileEntry) {
  auto it = m_includeMap.try_emplace(fileEntry->getUID(),
                                     std::make_unique<Inclusion>(*fileEntry));
  Inclusion *startedIncl = it.first->getSecond().get();
  m_includeStack.push_back(startedIncl);
}

void InclusionContext::endCurrentInclusion() {
  Inclusion &current = currentInclusion();
  m_includeStack.pop_back();
  currentInclusion().addInclusion(&current);
}

Inclusion &InclusionContext::currentInclusion() const {
  assert(hasInclusions() && "Empty stack of inclusions");
  return *m_includeStack.back();
}

bool InclusionContext::hasInclusions() const { return !m_includeStack.empty(); }

const Inclusion &InclusionContext::getInclusionOfFileUID(unsigned uid) const {
  auto it = m_includeMap.find(uid);
  assert(it != m_includeMap.end() && "No inclusion for file");

  return *it->getSecond();
}

} // namespace vf