#pragma once
#include "AnnotationStore.h"
#include "clang/Lex/Preprocessor.h"

namespace vf {

/**
 * Processes each comment encountered during parsing and keeps a reference to an
 * annotation store. If a comment represents a VeriFast annoation, it will also
 * be added to the annotation store.
 */
class CommentProcessor : public clang::CommentHandler {
  clang::FileID prevFile;
  unsigned prevBufferOffset;
  bool onlyWhitespace = true;

  AnnotationStore &_store;

  /**
   * @return whether or not all characters from 'start' up until 'end' only represent
   * white space.
   */
  static bool checkWhiteSpace(const char *start, const char *end) {
    for (; start < end; ++start) {
      if (!std::isspace(*start))
        return false;
    }
    return true;
  }

public:
  /**
   * Invoked when a comment is encountered. Checks if the comment is an
   * annotation. If so, it also adds it to the annotation store.
   * @param PP preprocessor.
   * @param comment source range of the comment.
   */
  bool HandleComment(clang::Preprocessor &PP, clang::SourceRange comment);

  explicit CommentProcessor(AnnotationStore &store) : _store(store) {}
  CommentProcessor(AnnotationStore &&store) = delete;
};
} // namespace vf