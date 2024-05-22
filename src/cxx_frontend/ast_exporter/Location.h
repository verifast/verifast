#pragma once

#include "stubs_ast.capnp.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/TypeLoc.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"
#include <optional>

namespace vf {

/**
 * @brief Location consisting of a line, column and unique identifier. The
 * unique identifier refers to the file the location is originating from.
 *
 */
struct Location {
  unsigned line;
  unsigned column;
  unsigned uid;

  void serialize(stubs::Loc::SrcPos::Builder builder) const;

  Location(unsigned line, unsigned column, unsigned uid)
      : line(line), column(column), uid(uid) {}
};

struct Range {
  Location begin;
  Location end;

  Range(Location begin, Location end) : begin(begin), end(end) {}
};

std::optional<Location>
ofSourceLocation(clang::SourceLocation loc,
                 const clang::SourceManager &sourceManager);

std::optional<Range> ofSourceRange(clang::SourceRange range,
                                   const clang::SourceManager &sourceManager);

clang::SourceRange getRange(const clang::Decl *decl);

clang::SourceRange getRange(const clang::Stmt *stmt);

clang::SourceRange getRange(const clang::Expr *expr);

clang::SourceRange getRange(clang::TypeLoc typeLoc);

const clang::FileEntry *
fileEntryOfLoc(clang::SourceLocation loc,
               const clang::SourceManager &sourceManager);

clang::Token getNextToken(clang::SourceLocation loc,
                          const clang::SourceManager &sourceManager,
                          const clang::LangOptions &langOpts);

clang::Token expectNextToken(clang::SourceLocation loc,
                             const clang::SourceManager &sourceManager,
                             const clang::LangOptions &langOpts,
                             clang::tok::TokenKind kind);

} // namespace vf