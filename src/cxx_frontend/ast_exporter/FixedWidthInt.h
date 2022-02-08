#pragma once
#include "loc_serializer.h"
#include "llvm/ADT/Optional.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

namespace vf {

struct FixedWidthInt {

  unsigned bits;
  bool isSigned;

  FixedWidthInt() = delete;
};

inline llvm::Optional<FixedWidthInt> getFixedWidthFromString(llvm::StringRef name) {
  if (name.equals("int8_t"))
    return llvm::Optional<FixedWidthInt>(std::move<FixedWidthInt>({8, false}));
  if (name.equals("int16_t"))
    return llvm::Optional<FixedWidthInt>(std::move<FixedWidthInt>({16, false}));
  if (name.equals("int32_t"))
    return llvm::Optional<FixedWidthInt>(std::move<FixedWidthInt>({32, false}));
  if (name.equals("int64_t"))
    return llvm::Optional<FixedWidthInt>(std::move<FixedWidthInt>({64, false}));
  if (name.equals("uint8_t"))
    return llvm::Optional<FixedWidthInt>(std::move<FixedWidthInt>({8, true}));
  if (name.equals("uint16_t"))
    return llvm::Optional<FixedWidthInt>(std::move<FixedWidthInt>({16, true}));
  if (name.equals("uint32_t"))
    return llvm::Optional<FixedWidthInt>(std::move<FixedWidthInt>({32, true}));
  if (name.equals("uint64_t"))
    return llvm::Optional<FixedWidthInt>(std::move<FixedWidthInt>({64, true}));
  return {};
}

}; // namespace vf