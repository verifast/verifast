#pragma once
#include <optional>
#include <string_view>

namespace vf {

struct FixedWidthInt {

  unsigned bits;
  bool isSigned;

  FixedWidthInt() = delete;
  explicit FixedWidthInt(unsigned bits, bool isSigned)
      : bits(bits), isSigned(isSigned) {}
};

std::optional<FixedWidthInt> getFixedWidthFromString(std::string_view name);

}; // namespace vf