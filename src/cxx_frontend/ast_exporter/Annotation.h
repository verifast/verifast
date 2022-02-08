#pragma once
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/ADT/Optional.h"

namespace vf {

/**
 * Represents a VeriFast annotation in the source code.
 */
class Annotation {
  clang::SourceRange _range;
  std::string _text;
  bool _isContractClauseLike;
  bool _isNewSeq;
  bool _isTruncating;

public:
  Annotation(clang::SourceRange &range, llvm::StringRef text,
             bool isContractClause, bool isTruncating, bool isNewSeq)
      : _range(range), _text(text), _isContractClauseLike(isContractClause),
        _isTruncating(isTruncating), _isNewSeq(isNewSeq) {}

public:
  clang::SourceRange getRange() const { return _range; }

  llvm::StringRef getText() const { return _text; }

  /**
   * @return whether or not this annotation can appear in a contract. I.e., the
   annotation starts with 'requires, 'ensures', 'terminates', ':', or
   'non_ghost_callers_only'. White space characters are not taken into account.
   */
  bool isContractClauseLike() const { return _isContractClauseLike; }

  /**
   * @return wether or not this annotation starts a new sequence of annotations.
   * I.e., the lines between this annotation and the previous one do not only
   * contain comments and/or white space.
   */
  bool isNewSeq() const { return _isNewSeq; }

  /**
   * @return wether or not this annotation is a truncating expression.
   */
  bool isTruncating() const { return _isTruncating; }
};

/**
 * Transforms the given text into an annotation if it represents one.
 * @param range the source range of the text.
 * @param text the text that may represent an annotation. This method assumes
 * that the given text is a valid C++ comment.
 * @param newSeq whether or not this annotation starts a new sequence.
 * @return an optional of an annotation.
 */
llvm::Optional<Annotation> annotationOf(clang::SourceRange range,
                                        llvm::StringRef text, bool isNewSeq);
} // namespace vf