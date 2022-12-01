#include "CommentProcessor.h"
#include "clang/Basic/FileManager.h"

namespace vf {

bool CommentProcessor::checkWhiteSpace(const char *start, const char *end) {
  for (; start < end; ++start) {
    if (!std::isspace(*start))
      return false;
  }
  return true;
}

bool CommentProcessor::HandleComment(clang::Preprocessor &PP,
                                     clang::SourceRange comment) {
  auto &SM = PP.getSourceManager();
  const char *begin = SM.getCharacterData(comment.getBegin());
  const char *end = SM.getCharacterData(comment.getEnd());

  auto locInfo = SM.getDecomposedLoc(comment.getBegin());
  auto fileID = locInfo.first;

  // We have entered a different file
  // Set offset to start of file
  if (fileID != m_prevFile) {
    m_prevFile = fileID;
    m_prevBufferOffset = 0;
  }

  unsigned currentOffset = locInfo.second;
  auto fileBuffer = SM.getBufferData(m_prevFile);
  m_onlyWhitespace = checkWhiteSpace(fileBuffer.data() + m_prevBufferOffset,
                                     fileBuffer.data() + currentOffset);

  if (*(begin + 2) == '~') {
    m_store.addFailDirective(
        Text(comment, llvm::StringRef(begin, end - begin)));
  } else {

    auto annOpt = annotationOf(
        comment, llvm::StringRef(begin, end - begin),
        /* annotation at the start of the file */ m_prevBufferOffset ==
                currentOffset ||
            !m_onlyWhitespace);
    if (annOpt) {
      m_store.add(std::move(*annOpt), SM);
    }
  }

  m_prevBufferOffset = currentOffset + end - begin;

  return false;
}
} // namespace vf