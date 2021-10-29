#include "CommentProcessor.h"
#include "clang/Basic/FileManager.h"

namespace vf {
bool CommentProcessor::HandleComment(clang::Preprocessor &PP,
                                     clang::SourceRange comment) {
  auto &SM = PP.getSourceManager();
  const char *begin = SM.getCharacterData(comment.getBegin());
  const char *end = SM.getCharacterData(comment.getEnd());

  auto locInfo = SM.getDecomposedLoc(comment.getBegin());
  auto fileID = locInfo.first;

  // We have entered a different file
  // Set offset to start of file
  if (fileID != prevFile) {
    prevFile = fileID;
    prevBufferOffset = 0;
  }

  unsigned currentOffset = locInfo.second;
  auto fileBuffer = SM.getBufferData(prevFile);
  onlyWhitespace = checkWhiteSpace(fileBuffer.data() + prevBufferOffset,
                                   fileBuffer.data() + currentOffset);

  auto annOpt =
      annotationOf(comment, llvm::StringRef(begin, end - begin),
                   /* annotation at the start of the file */ prevBufferOffset ==
                           currentOffset ||
                       !onlyWhitespace);
  if (annOpt) {
    _store.add(std::move(*annOpt), SM);
  }

  prevBufferOffset = currentOffset + end - begin;

  return false;
}
} // namespace vf