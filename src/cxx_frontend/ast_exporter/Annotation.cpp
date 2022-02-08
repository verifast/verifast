#include "Annotation.h"

namespace vf {

class GhostCodeAnalyzer {
  llvm::StringRef _text;
  llvm::StringRef::iterator _pos;
  bool _isAnnotationLike;
  bool _isContractClauseLike = false;
  bool _checkedForContractClause = false;
  bool _isTruncating = false;
  bool _checkedForTruncating = false;

  // Check for ghost symbols. `/*@*/` is allowed so we don't silently ignore it
  // and VeriFast can throw a parse error.
  static bool isAnnotationLike(llvm::StringRef text) {
    auto begin = text.begin();
    auto end = text.end();
    return text.size() > 3 && *(begin + 2) == '@' &&
           (*(begin + 1) == '/' || *(end - 3) == '@');
  }

  void skipWhitespace() {
    for (; _pos != _text.end() && isspace(*_pos); ++_pos);
  }

  bool startsWith(llvm::StringRef prefix) {
    auto pos = prefix.begin();
    for (; _pos != _text.end() && pos != prefix.end() && *_pos == *pos; ++_pos, ++pos);
    return pos == prefix.end();
  }

public:
  explicit GhostCodeAnalyzer(llvm::StringRef text)
      : _text(text), _pos(text.begin()), _isAnnotationLike(isAnnotationLike(text)) {}

  bool isAnnotationLike() { return _isAnnotationLike; }

  bool isContractClauseLike() {
    if (_checkedForContractClause)
      return _isContractClauseLike;
    std::string checks[] = {"requires", "ensures", "terminates", ":",
                                   "non_ghost_callers_only"};
    for (const auto &prefix : checks) {
      _pos = _text.begin() + 3;
      skipWhitespace();
      if (startsWith(prefix)) {
        _isContractClauseLike = true;
        break;
      }
    }
    _checkedForContractClause = true;
    return _isContractClauseLike;
  }

  bool isTruncating() {
    if (_checkedForTruncating)
      return _isTruncating;
    
    _checkedForTruncating = true;
    _pos = _text.begin() + 3;

    skipWhitespace();
    if (! startsWith("truncating")) {
      _isTruncating = false;
      return false;
    }

    skipWhitespace();
    if (_pos == _text.end()) {
      _isTruncating = true;
      return true;
    }

    if (startsWith("@*/")) {
      _isTruncating = true;
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