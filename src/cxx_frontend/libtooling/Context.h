#pragma once
#include "Inclusion.h"
#include "kj/common.h"
#include "loc_serializer.h"
#include <unordered_map>

namespace vf {
class Context {
  using get_first_decl_loc_fn = std::function<llvm::Optional<clang::SourceLocation>(unsigned)>;

  std::unordered_map<unsigned, Inclusion> _includesMap;
  llvm::SmallVector<Inclusion *, 8> _includesStack;

  friend class ContextFreePPCallbacks;
  Inclusion *currentInclusion() {
    assert(hasInclusions() && "Empty stack of inclusions");
    return _includesStack.back();
  }

  void serializeInclDirectivesCore(
      capnp::List<stubs::Include, capnp::Kind::STRUCT>::Builder &builder,
      const clang::SourceManager &SM,
      const llvm::ArrayRef<InclDirective> inclDirectives,
      get_first_decl_loc_fn &getFirstDeclLocOpt,
      unsigned fd) const;

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

  void addInclDirective(clang::SourceRange range, clang::StringRef fileName,
                        const clang::FileEntry &fileEntry, bool isAngled) {
    currentInclusion()->addInclDirective(range, fileName, fileEntry.getUID(),
                                         isAngled);
  }

  void endInclusion() {
    auto ended = currentInclusion();
    _includesStack.pop_back();
    currentInclusion()->addInclusion(ended);
  }

  void serializeTUInclDirectives(stubs::TU::Builder &builder,
                                 const clang::SourceManager &SM,
                                get_first_decl_loc_fn &getFirstDeclLocOpt) const;
};
} // namespace vf