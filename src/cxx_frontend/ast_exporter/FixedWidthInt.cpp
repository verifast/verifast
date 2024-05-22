#include "FixedWidthInt.h"
#include <tuple>

namespace {
std::tuple<std::string_view, bool, unsigned> constexpr mappings[] = {
    {"int8_t", true, 8},     {"int16_t", true, 16},   {"int32_t", true, 32},
    {"int64_t", true, 64},   {"uint8_t", false, 8},   {"uint16_t", false, 16},
    {"uint32_t", false, 32}, {"uint64_t", false, 64},
};
}

namespace vf {
std::optional<FixedWidthInt> getFixedWidthFromString(std::string_view name) {
  for (const auto &mapping : mappings) {
    if (std::get<std::string_view>(mapping).compare(name) == 0) {
      return std::make_optional<FixedWidthInt>(std::get<unsigned>(mapping),
                                               std::get<bool>(mapping));
    }
  }
  return {};
}
} // namespace vf