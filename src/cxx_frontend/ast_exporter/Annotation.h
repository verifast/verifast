#pragma once

#include "Text.h"
#include "clang/Basic/SourceLocation.h"

namespace vf {

class Annotation : public Text {
public:
  enum Kind {
    Ann_Unknown,
    Ann_ContractClause,
    Ann_Truncating,
    Ann_Include,
    Ann_Other,
  };

  Kind getKind() const { return m_kind; }

  clang::SourceLocation getNextTokenLoc() const { return m_nextTokenLoc; }

  bool is(Kind kind) const { return m_kind == kind; }

  template <Kind K> struct Predicate {
    bool operator()(const Annotation &annotation) const {
      return annotation.is(K);
    }
  };

  Annotation(Kind kind, clang::SourceRange range, std::string_view text,
             clang::SourceLocation nextTokenLoc)
      : Text(range, text), m_kind(kind), m_nextTokenLoc(nextTokenLoc) {}

  Annotation(const Annotation &) = default;

private:
  Kind m_kind;
  clang::SourceLocation m_nextTokenLoc;
};

} // namespace vf