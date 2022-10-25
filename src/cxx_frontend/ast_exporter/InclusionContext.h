#pragma once
#include "Inclusion.h"
#include "kj/common.h"
#include "loc_serializer.h"
#include <unordered_map>

namespace vf {
class InclusionContext {
  using get_first_decl_loc_fn =
      std::function<llvm::Optional<clang::SourceLocation>(unsigned)>;

  std::unordered_map<unsigned, Inclusion> m_includesMap;
  llvm::SmallVector<Inclusion *, 8> m_includesStack;

  friend class ContextFreePPCallbacks;
  Inclusion *currentInclusion() {
    assert(hasInclusions() && "Empty stack of inclusions");
    return m_includesStack.back();
  }

  void serializeInclDirectivesCore(
      capnp::List<stubs::Include, capnp::Kind::STRUCT>::Builder &builder,
      const clang::SourceManager &SM,
      const llvm::ArrayRef<InclDirective> inclDirectives,
      get_first_decl_loc_fn &getFirstDeclLocOpt, unsigned fd) const;

public:
  explicit InclusionContext() {}

  KJ_DISALLOW_COPY(InclusionContext);

  bool hasInclusions() { return !m_includesStack.empty(); }

  void startInclusion(const clang::FileEntry &fileEntry) {
    auto it = m_includesMap.emplace(fileEntry.getUID(), fileEntry);
    auto &startedIncl = it.first->second;
    m_includesStack.push_back(&startedIncl);
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
    m_includesStack.pop_back();
    currentInclusion()->addInclusion(ended);
  }

  void
  serializeTUInclDirectives(stubs::TU::Builder &builder,
                            const clang::SourceManager &SM,
                            get_first_decl_loc_fn &getFirstDeclLocOpt) const;
};
} // namespace vf