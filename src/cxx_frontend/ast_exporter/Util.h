#pragma once

#include "stubs_ast.capnp.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"

namespace vf {

struct LCF {
  unsigned int l;
  unsigned int c;
  unsigned int f;
};

/**
 * Decompose the line, column and file unique identifier from a source location.
 * The result will be placed in the given \p lcf if the given location \p loc is
 * valid and not coming from a 'real' file (not a system file).
 *
 * @param loc source location to decompose.
 * @param SM source manager.
 * @param[out] lcf struct to place the line, column and file uniques identifier
 * in.
 * @return true if the given location \p loc was valid and could be decomposed.
 * @return false if the given location \p was incalid and it was not possible to
 * decompose it.
 */
bool decomposeLocToLFC(const clang::SourceLocation &loc,
                       const clang::SourceManager &SM, LCF &lcf);

inline void serializeSrcPos(stubs::Loc::SrcPos::Builder &builder, LCF lcf) {
  builder.setL(lcf.l);
  builder.setC(lcf.c);
  builder.setFd(lcf.f);
}

void serializeSrcRange(stubs::Loc::Builder &builder,
                       const clang::SourceRange &range,
                       const clang::SourceManager &SM);

inline const clang::FileEntry *getFileEntry(const clang::SourceLocation &loc,
                                            const clang::SourceManager &SM) {
  auto id = SM.getFileID(SM.getExpansionLoc(loc));
  return SM.getFileEntryForID(id);
}

} // namespace vf