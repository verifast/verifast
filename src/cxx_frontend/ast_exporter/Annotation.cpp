#include "Annotation.h"

namespace vf {

class GhostCodeAnalyzer {
  llvm::StringRef m_text;
  llvm::StringRef::iterator m_pos;
  bool m_isAnnotationLike;
  bool m_isContractClauseLike = false;
  bool m_checkedForContractClause = false;
  bool m_isTruncating = false;
  bool m_checkedForTruncating = false;

  // Check for ghost symbols. `/*@*/` is allowed so we don't silently ignore it
  // and VeriFast can throw a parse error.
  static bool isAnnotationLike(llvm::StringRef text) {
    auto begin = text.begin();
    auto end = text.end();
    return text.size() > 3 && *(begin + 2) == '@' &&
           (*(begin + 1) == '/' || *(end - 3) == '@');
  }

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

public:
  explicit GhostCodeAnalyzer(llvm::StringRef text)
      : m_text(text), m_pos(text.begin()),
        m_isAnnotationLike(isAnnotationLike(text)) {}

  bool isAnnotationLike() { return m_isAnnotationLike; }

  bool isContractClauseLike() {
    if (m_checkedForContractClause)
      return m_isContractClauseLike;
    std::string checks[] = {"requires", "ensures", "terminates", ":",
                            "non_ghost_callers_only"};
    for (const auto &prefix : checks) {
      m_pos = m_text.begin() + 3;
      skipWhitespace();
      if (startsWith(prefix)) {
        m_isContractClauseLike = true;
        break;
      }
    }
    m_checkedForContractClause = true;
    return m_isContractClauseLike;
  }

  bool isTruncating() {
    if (m_checkedForTruncating)
      return m_isTruncating;

    m_checkedForTruncating = true;
    m_pos = m_text.begin() + 3;

    skipWhitespace();
    if (!startsWith("truncating")) {
      m_isTruncating = false;
      return false;
    }

    skipWhitespace();
    if (m_pos == m_text.end()) {
      m_isTruncating = true;
      return true;
    }

    if (startsWith("@*/")) {
      m_isTruncating = true;
      return true;
    }

    return false;
  }
};

// Assumes that the given text is a valid C++ comment.
llvm::Optional<Annotation> annotationOf(clang::SourceRange range,
                                        llvm::StringRef text, bool isNewSeq) {
  llvm::Optional<Annotation> result;
  GhostCodeAnalyzer gca(text);
  if (gca.isAnnotationLike()) {
    bool isContractClauseLike = gca.isContractClauseLike();
    bool isTruncating = isContractClauseLike ? false : gca.isTruncating();
    result.emplace(range, text, isContractClauseLike, isTruncating, isNewSeq);
  }
  return result;
}
} // namespace vf