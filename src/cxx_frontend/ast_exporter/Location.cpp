#include "Location.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/TypeLocVisitor.h"
#include "clang/Lex/Lexer.h"

namespace vf {

void Location::serialize(stubs::Loc::SrcPos::Builder builder) const {
  builder.setL(line);
  builder.setC(column);
  builder.setFd(uid);
}

std::optional<Location>
ofSourceLocation(clang::SourceLocation loc,
                 const clang::SourceManager &sourceManager) {
  if (loc.isInvalid()) {
    return {};
  }

  std::pair<clang::FileID, unsigned> locPair =
      sourceManager.getDecomposedLoc(sourceManager.getSpellingLoc(loc));
  const clang::FileEntry *fileEntry =
      sourceManager.getFileEntryForID(locPair.first);

  if (!fileEntry) {
    return {};
  }

  unsigned uid = fileEntry->getUID();
  unsigned line = sourceManager.getLineNumber(locPair.first, locPair.second);
  unsigned col = sourceManager.getColumnNumber(locPair.first, locPair.second);

  return std::make_optional<Location>(line, col, uid);
}

std::optional<Range> ofSourceRange(clang::SourceRange range,
                                   const clang::SourceManager &sourceManager) {
  if (range.isInvalid()) {
    return {};
  }

  std::optional<Location> begin =
      ofSourceLocation(range.getBegin(), sourceManager);

  if (!begin) {
    return {};
  }

  std::optional<Location> end = ofSourceLocation(range.getEnd(), sourceManager);

  if (!end) {
    return {};
  }

  return std::make_optional<Range>(*begin, *end);
}

namespace {

// Visitors to retrieve the source range of declarations, statements,
// expressions and type locations. Returns an invalid range for *item* if no
// Visit method is defined for *item*.

struct DeclRangeVisitor
    : public clang::ConstDeclVisitor<DeclRangeVisitor, clang::SourceRange> {
  clang::SourceRange VisitFunctionDecl(const clang::FunctionDecl *decl) {
    return decl->getNameInfo().getSourceRange();
  }
};

struct StmtRangeVisitor
    : public clang::ConstStmtVisitor<StmtRangeVisitor, clang::SourceRange> {};

struct ExprRangeVisitor
    : public clang::ConstStmtVisitor<ExprRangeVisitor, clang::SourceRange> {};

struct TypeLocRangeVisitor
    : public clang::TypeLocVisitor<TypeLocRangeVisitor, clang::SourceRange> {};

DeclRangeVisitor declRangeVisitor;
StmtRangeVisitor stmtRangeVisitor;
ExprRangeVisitor exprRangeVisitor;
TypeLocRangeVisitor typeLocRangeVisitor;

} // namespace

clang::SourceRange getRange(const clang::Decl *decl) {
  if (!decl || decl->isImplicit()) {
    return {};
  }

  clang::SourceRange range = declRangeVisitor.Visit(decl);
  if (range.isInvalid()) {
    return decl->getSourceRange();
  }

  return range;
}

clang::SourceRange getRange(const clang::Stmt *stmt) {
  if (!stmt) {
    return {};
  }
  clang::SourceRange range = stmtRangeVisitor.Visit(stmt);

  if (range.isInvalid()) {
    return stmt->getSourceRange();
  }

  return range;
}

clang::SourceRange getRange(const clang::Expr *expr) {
  if (!expr) {
    return {};
  }
  clang::SourceRange range = exprRangeVisitor.Visit(expr);

  if (range.isInvalid()) {
    return expr->getSourceRange();
  }

  return range;
}

clang::SourceRange getRange(clang::TypeLoc typeLoc) {
  clang::SourceRange range = typeLocRangeVisitor.Visit(typeLoc);

  if (range.isInvalid()) {
    return typeLoc.getSourceRange();
  }

  return range;
}

const clang::FileEntry *
fileEntryOfLoc(clang::SourceLocation loc,
               const clang::SourceManager &sourceManager) {
  clang::SourceLocation expansionLoc = sourceManager.getExpansionLoc(loc);
  clang::FileID id = sourceManager.getFileID(expansionLoc);
  return sourceManager.getFileEntryForID(id);
}

clang::Token getNextToken(clang::SourceLocation loc,
                          const clang::SourceManager &sourceManager,
                          const clang::LangOptions &langOpts) {
  std::optional<clang::Token> nextToken =
      clang::Lexer::findNextToken(loc, sourceManager, langOpts);
  assert(nextToken && "No next token");
  return *nextToken;
}

clang::Token expectNextToken(clang::SourceLocation loc,
                             const clang::SourceManager &sourceManager,
                             const clang::LangOptions &langOpts,
                             clang::tok::TokenKind kind) {
  clang::Token nextToken(getNextToken(loc, sourceManager, langOpts));
  assert(nextToken.is(kind) && "Expected other token");
  return nextToken;
}

} // namespace vf