#include "Util.h"

namespace vf {

bool decomposeLocToLFC(const clang::SourceLocation &loc,
                       const clang::SourceManager &SM, LCF &lcf) {
  auto decLoc = SM.getDecomposedLoc(SM.getSpellingLoc(loc));
  auto fileEntry = SM.getFileEntryForID(decLoc.first);

  if (!fileEntry || !fileEntry->isValid())
    return false;

  auto uid = fileEntry->getUID();
  auto line = SM.getLineNumber(decLoc.first, decLoc.second);
  auto col = SM.getColumnNumber(decLoc.first, decLoc.second);
  lcf.l = line;
  lcf.c = col;
  lcf.f = uid;
  return true;
}

void serializeSrcRange(stubs::Loc::Builder &builder,
                       const clang::SourceRange &range,
                       const clang::SourceManager &SM) {
  auto rBegin = range.getBegin();
  auto rEnd = range.getEnd();
  LCF lcf;
  if (rBegin.isValid() && decomposeLocToLFC(rBegin, SM, lcf)) {
    auto start = builder.initStart();
    serializeSrcPos(start, lcf);
  }
  if (rEnd.isValid() && decomposeLocToLFC(rEnd, SM, lcf)) {
    auto end = builder.initEnd();
    serializeSrcPos(end, lcf);
  }
}

} // namespace vf