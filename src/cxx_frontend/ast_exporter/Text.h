#pragma once
#include "clang/Basic/SourceLocation.h"
#include <string>
#include <string_view>

namespace vf {
class Text {
public:
  clang::SourceRange getRange() const { return m_range; }

  std::string_view getText() const { return m_text; }

  Text(clang::SourceRange range, std::string_view text)
      : m_range(range), m_text(text) {}

private:
  clang::SourceRange m_range;
  std::string m_text;
};
} // namespace vf