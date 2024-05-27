#include "CommentProcessor.h"

namespace vf {

bool CommentProcessor::HandleComment(clang::Preprocessor &preprocessor,
                                     clang::SourceRange comment) {
  const clang::SourceManager &sourceManager = preprocessor.getSourceManager();
  const char *begin = sourceManager.getCharacterData(comment.getBegin());
  const char *end = sourceManager.getCharacterData(comment.getEnd());

  std::string_view text(begin, end - begin);

  if (text.starts_with("//~")) {
    text.remove_prefix(3);
    m_annotationManager.addFailDirective(Text(comment, text));
    return false;
  }

  std::optional<Annotation> annotationOpt =
      m_annotationManager.analyzeText(comment, text);
  if (annotationOpt) {
    m_annotationManager.addAnnotation(std::move(*annotationOpt));
    return false;
  }

  return false;
}

} // namespace vf