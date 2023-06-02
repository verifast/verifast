#pragma once
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Optional.h"

namespace vf {

struct FixedWidthInt {

  unsigned bits;
  bool isSigned;

  FixedWidthInt() = delete;
  explicit FixedWidthInt(unsigned bits, bool isSigned)
      : bits(bits), isSigned(isSigned) {}
};

llvm::Optional<FixedWidthInt> getFixedWidthFromString(llvm::StringRef name);

}; // namespace vf
