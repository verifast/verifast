#pragma once

#include "AnnotationManager.h"
#include "clang/Lex/Preprocessor.h"

namespace vf {

/**
 * @brief Processes all comments of a translation unit and adds them to a
 * annotation manager if the processed text appears to be an annotation.
 *
 */
class CommentProcessor : public clang::CommentHandler {
public:
  bool HandleComment(clang::Preprocessor &preprocessor,
                     clang::SourceRange comment) override;

  explicit CommentProcessor(AnnotationManager &annotationManager)
      : m_annotationManager(annotationManager) {}

private:
  AnnotationManager &m_annotationManager;
};

} // namespace vf