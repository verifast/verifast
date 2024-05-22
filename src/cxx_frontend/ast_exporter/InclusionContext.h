#pragma once
#include "Inclusion.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"

namespace vf {

class InclusionContext {
public:
  void startInclusionForFile(const clang::FileEntry *fileEntry);

  void endCurrentInclusion();

  Inclusion &currentInclusion() const;

  bool hasInclusions() const;

  explicit InclusionContext() = default;

  const Inclusion &getInclusionOfFileUID(unsigned uid) const;

private:
  llvm::DenseMap<unsigned, std::unique_ptr<Inclusion>> m_includeMap;
  llvm::SmallVector<Inclusion *> m_includeStack;
};

} // namespace vf