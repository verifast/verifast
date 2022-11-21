#include "FixedWidthInt.h"
#include "llvm/ADT/StringRef.h"

namespace vf {
llvm::Optional<FixedWidthInt> getFixedWidthFromString(llvm::StringRef name) {
  llvm::Optional<FixedWidthInt> result;
  if (name.equals("int8_t")) {
    result.emplace(8, true);
    return result;
  }
  if (name.equals("int16_t")) {
    result.emplace(16, true);
    return result;
  }
  if (name.equals("int32_t")) {
    result.emplace(32, true);
    return result;
  }
  if (name.equals("int64_t")) {
    result.emplace(64, true);
    return result;
  }
  if (name.equals("uint8_t")) {
    result.emplace(8, false);
    return result;
  }
  if (name.equals("uint16_t")) {
    result.emplace(16, false);
    return result;
  }
  if (name.equals("uint32_t")) {
    result.emplace(32, false);
    return result;
  }
  if (name.equals("uint64_t")) {
    result.emplace(64, false);
    return result;
  }
  return result;
}
} // namespace vf