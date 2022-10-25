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
  clang::SourceRange m_range;
  std::string m_text;
  bool m_isContractClauseLike;
  bool m_isNewSeq;
  bool m_isTruncating;

public:
  Annotation(clang::SourceRange &range, llvm::StringRef text,
             bool isContractClause, bool isTruncating, bool isNewSeq)
      : m_range(range), m_text(text), m_isContractClauseLike(isContractClause),
        m_isTruncating(isTruncating), m_isNewSeq(isNewSeq) {}

public:
  clang::SourceRange getRange() const { return m_range; }

  llvm::StringRef getText() const { return m_text; }

  /**
   * @return whether or not this annotation can appear in a contract. I.e., the
   annotation starts with 'requires, 'ensures', 'terminates', ':', or
   'non_ghost_callers_only'. White space characters are not taken into account.
   */
  bool isContractClauseLike() const { return m_isContractClauseLike; }

  /**
   * @return wether or not this annotation starts a new sequence of annotations.
   * I.e., the lines between this annotation and the previous one do not only
   * contain comments and/or white space.
   */
  bool isNewSeq() const { return m_isNewSeq; }

  /**
   * @return wether or not this annotation is a truncating expression.
   */
  bool isTruncating() const { return m_isTruncating; }
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