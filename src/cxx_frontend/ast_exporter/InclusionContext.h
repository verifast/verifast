#pragma once
#include "Inclusion.h"
#include "Util.h"
#include "kj/common.h"
#include <unordered_map>

namespace vf {
class InclusionContext {
  std::unordered_map<unsigned, Inclusion> m_includesMap;
  llvm::SmallVector<Inclusion *> m_includesStack;

  friend class ContextFreePPCallbacks;
  Inclusion *currentInclusion() {
    assert(hasInclusions() && "Empty stack of inclusions");
    return m_includesStack.back();
  }

  void serializeInclDirectivesCore(
      capnp::List<stubs::Include, capnp::Kind::STRUCT>::Builder &builder,
      const clang::SourceManager &SM,
      const llvm::ArrayRef<IncludeDirective> inclDirectives, unsigned fd) const;

public:
  explicit InclusionContext() {}

  KJ_DISALLOW_COPY(InclusionContext);

  const Inclusion &getInclusionForFD(unsigned fd) const {
    return m_includesMap.at(fd);
  }

  bool hasInclusions() { return !m_includesStack.empty(); }

  void startInclusion(const clang::FileEntry &fileEntry);

  void addRealInclDirective(clang::SourceRange range, clang::StringRef fileName,
                            const clang::FileEntry &fileEntry, bool isAngled) {
    currentInclusion()->addRealInclDirective(range, fileName,
                                             fileEntry.getUID(), isAngled);
  }

  void addGhostInclDirective(const clang::FileEntry *entry, Annotation &ann) {
    auto uid = entry->getUID();
    assert(m_includesMap.contains(uid) &&
           "File has not been preprocessed and added to inclusion context");
    m_includesMap.at(uid).addGhostInclDirective(ann);
  }

  void endInclusion();

  void serializeTUInclDirectives(stubs::TU::Builder &builder,
                                 const clang::SourceManager &SM,
                                 AstSerializer &serializer) const;
};
} // namespace vf