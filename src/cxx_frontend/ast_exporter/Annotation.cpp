#include "Annotation.h"

namespace vf {

class GhostCodeAnalyzer {
  llvm::StringRef m_text;
  llvm::StringRef::iterator m_pos;
  Annotation::Kind m_kind;

  void skipWhitespace() {
    for (; m_pos != m_text.end() && isspace(*m_pos); ++m_pos)
      ;
  }

  bool startsWith(llvm::StringRef prefix) {
    auto pos = prefix.begin();
    for (; m_pos != m_text.end() && pos != prefix.end() && *m_pos == *pos;
         ++m_pos, ++pos)
      ;
    return pos == prefix.end();
  }

  bool kindIsNotUnknown() { return m_kind != Annotation::Kind::Ann_Unknown; }

  bool isContractClauseLike() {
    if (kindIsNotUnknown())
      return m_kind == Annotation::Kind::Ann_ContractClause;

    std::string checks[] = {"requires", "ensures", "terminates", ":",
                            "non_ghost_callers_only"};
    for (const auto &prefix : checks) {
      m_pos = m_text.begin() + 3;
      skipWhitespace();
      if (startsWith(prefix)) {
        m_kind = Annotation::Kind::Ann_ContractClause;
        return true;
      }
    }
    return false;
  }

  bool isTruncating() {
    if (kindIsNotUnknown())
      return m_kind == Annotation::Kind::Ann_Truncating;

    m_pos = m_text.begin() + 3;

    skipWhitespace();
    if (!startsWith("truncating")) {
      return false;
    }

    skipWhitespace();
    if (m_pos == m_text.end()) {
      m_kind = Annotation::Kind::Ann_Truncating;
      return true;
    }

    if (startsWith("@*/")) {
      m_kind = Annotation::Kind::Ann_Truncating;
      return true;
    }

    return false;
  }

  bool isInclude() {
    if (kindIsNotUnknown())
      return m_kind == Annotation::Kind::Ann_Include;

    m_pos = m_text.begin() + 3;

    skipWhitespace();
    if (startsWith("#include")) {
      m_kind = Annotation::Kind::Ann_Include;
      return true;
    }

    return false;
  }

public:
  explicit GhostCodeAnalyzer(llvm::StringRef text)
      : m_text(text), m_pos(text.begin()),
        m_kind(Annotation::Kind::Ann_Unknown) {}

  Annotation::Kind getKind() {
    if (kindIsNotUnknown()) return m_kind;
    if (isTruncating()) return m_kind;
    if (isContractClauseLike()) return m_kind;
    if (isInclude()) return m_kind;

    m_kind = Annotation::Kind::Ann_other;
    return m_kind;
  }

  // Check for ghost symbols. `/*@*/` is allowed so we don't silently ignore it
  // and VeriFast can throw a parse error.
  static bool isAnnotationLike(llvm::StringRef text) {
    auto begin = text.begin();
    auto end = text.end();
    return text.size() > 3 && *(begin + 2) == '@' &&
           (*(begin + 1) == '/' || *(end - 3) == '@');
  }
};

// Assumes that the given text is a valid C++ comment.
llvm::Optional<Annotation> annotationOf(clang::SourceRange range,
                                        llvm::StringRef text, bool isNewSeq) {
  llvm::Optional<Annotation> result;
  if (!GhostCodeAnalyzer::isAnnotationLike(text))
    return result;

  GhostCodeAnalyzer gca(text);
  auto kind = gca.getKind();
  result.emplace(range, text, kind, isNewSeq);
  return result;
}
} // namespace vf