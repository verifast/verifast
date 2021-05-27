#pragma once
#include "Inclusion.h"
#include "kj/common.h"
#include "llvm/ADT/SmallVector.h"
#include <unordered_map>

namespace vf {
class Context {
  std::unordered_map<unsigned, Inclusion> _includesMap;
  llvm::SmallVector<Inclusion *, 8> _includesStack;

  friend class ContextFreePPCallbacks;
  Inclusion *currentInclusion() {
    assert(hasInclusions() && "Empty stack of inclusions");
    return _includesStack.back();
  }

public:
  explicit Context() {}

  KJ_DISALLOW_COPY(Context);

  bool hasInclusions() { return !_includesStack.empty(); }

  void startInclusion(const clang::FileEntry &fileEntry) {
    auto it = _includesMap.emplace(fileEntry.getUID(), fileEntry);
    auto &startedIncl = it.first->second;
    _includesStack.push_back(&startedIncl);
    // TODO: what if we start an inclusion that we already processed? -> does
    // not have header guards; then it.second will be false
  }

  void endInclusion() {
    auto ended = currentInclusion();
    _includesStack.pop_back();
    currentInclusion()->addInclusion(ended);
  }
};
} // namespace vf