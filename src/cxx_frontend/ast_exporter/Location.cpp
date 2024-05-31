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

  clang::SourceRange VisitVarDecl(const clang::VarDecl *decl) {
    return decl->getLocation();
  }
};

struct StmtRangeVisitor
    : public clang::ConstStmtVisitor<StmtRangeVisitor, clang::SourceRange> {
  clang::SourceRange VisitSwitchStmt(const clang::SwitchStmt *stmt) {
    return stmt->getSwitchLoc();
  }

  clang::SourceRange VisitIfStmt(const clang::IfStmt *stmt) {
    return stmt->getIfLoc();
  }

  clang::SourceRange VisitDeclStmt(const clang::DeclStmt *stmt) {
    DeclRangeVisitor visitor;
    return visitor.Visit(*stmt->decl_begin());
  }
};

struct ExprRangeVisitor
    : public clang::ConstStmtVisitor<ExprRangeVisitor, clang::SourceRange> {
  clang::SourceRange
  VisitBinaryOperator(const clang::BinaryOperator *binOperator) {
    return binOperator->getOperatorLoc();
  }

  clang::SourceRange VisitCallExpr(const clang::CallExpr *expr) {
    return expr->getCallee()->getSourceRange();
  }
};

struct TypeLocRangeVisitor
    : public clang::TypeLocVisitor<TypeLocRangeVisitor, clang::SourceRange> {};

DeclRangeVisitor declRangeVisitor;
StmtRangeVisitor stmtRangeVisitor;
ExprRangeVisitor exprRangeVisitor;
TypeLocRangeVisitor typeLocRangeVisitor;

template <typename Node, typename Visitor>
clang::SourceRange getRange(const Node *node, Visitor &visitor) {
  clang::SourceRange range = visitor.Visit(node);
  if (range.isInvalid()) {
    return node->getSourceRange();
  }
  return range;
}

} // namespace

clang::SourceRange getRange(const clang::Decl *decl) {
  if (!decl || decl->isImplicit()) {
    return {};
  }
  return getRange(decl, declRangeVisitor);
}

clang::SourceRange getRange(const clang::Stmt *stmt) {
  if (!stmt) {
    return {};
  }
  return getRange(stmt, stmtRangeVisitor);
}

clang::SourceRange getRange(const clang::Expr *expr) {
  if (!expr) {
    return {};
  }
  return getRange(expr, exprRangeVisitor);
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
  auto s = &Location::serialize;
}

} // namespace vf