#pragma once

#include "stubs_ast.capnp.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/FileManager.h"

inline void serializeSrcPos(stubs::Loc::SrcPos::Builder &builder,
                            const clang::SourceLocation &loc,
                            const clang::SourceManager &SM) {
  auto decLoc = SM.getDecomposedLoc(SM.getSpellingLoc(loc));
  auto line = SM.getLineNumber(decLoc.first, decLoc.second);
  auto col = SM.getColumnNumber(decLoc.first, decLoc.second);
  auto fileEntry = SM.getFileEntryForID(decLoc.first);
  builder.setL(line);
  builder.setC(col);
  builder.setFd(fileEntry->getUID());
}

inline void serializeSrcRange(stubs::Loc::Builder &builder,
                              const clang::SourceRange &range,
                              const clang::SourceManager &SM) {
  auto start = builder.initStart();
  auto end = builder.initEnd();
  auto rBegin = range.getBegin();
  auto rEnd = range.getEnd();
  if (rBegin.isValid()) serializeSrcPos(start, rBegin, SM);
  if (rEnd.isValid()) serializeSrcPos(end, rEnd, SM);
}