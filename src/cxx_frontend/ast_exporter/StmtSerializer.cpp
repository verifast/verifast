#include "AstSerializer.h"
#include "clang/AST/Stmt.h"

namespace vf {

bool StmtSerializer::VisitCompoundStmt(const clang::CompoundStmt *stmt) {
  StmtListSerializer stmtListSerializer(
      capnp::Orphanage::getForMessageContaining(m_builder), m_serializer);
  auto &store = m_serializer.getAnnStore();
  auto &SM = getSourceManager();
  llvm::SmallVector<Annotation> anns;

  for (auto s : stmt->body()) {
    store.getUntilLoc(anns, s->getBeginLoc(), SM);
    stmtListSerializer << anns << s;
    anns.clear();
  }

  store.getUntilLoc(anns, stmt->getRBracLoc(), SM);
  stmtListSerializer << anns;

  auto comp = m_builder.initCompound();
  auto children = comp.initStmts(stmtListSerializer.size());
  stmtListSerializer.adoptListToBuilder(children);

  auto rBrace = comp.initRBrace();
  auto rBraceLoc = stmt->getRBracLoc();
  serializeSourceRange(rBrace, rBraceLoc, SM, getContext().getLangOpts());

  return true;
}

bool StmtSerializer::VisitReturnStmt(const clang::ReturnStmt *stmt) {
  auto ret = m_builder.initReturn();
  auto retVal = stmt->getRetValue();

  if (retVal) {
    auto retExpr = ret.initExpr();
    m_serializer.serializeExpr(retExpr, retVal);
  }
  return true;
}

bool StmtSerializer::VisitDeclStmt(const clang::DeclStmt *stmt) {
  auto nbChildren = std::distance(stmt->decl_begin(), stmt->decl_end());
  auto children = m_builder.initDecl(nbChildren);

  size_t i(0);
  for (auto it = stmt->decl_begin(); it != stmt->decl_end(); ++it, ++i) {
    auto child = children[i];
    m_serializer.serializeDecl(child, *it);
  }
  return true;
}

bool StmtSerializer::VisitExpr(const clang::Expr *stmt) {
  auto expr = m_builder.initExpr();

  m_serializer.serializeExpr(expr, stmt);
  return true;
}

bool StmtSerializer::VisitIfStmt(const clang::IfStmt *stmt) {
  auto ifStmt = m_builder.initIf();

  auto cond = ifStmt.initCond();
  m_serializer.serializeExpr(cond, stmt->getCond());

  auto then = ifStmt.initThen();
  m_serializer.serializeStmt(then, stmt->getThen());

  if (stmt->hasElseStorage()) {
    auto el = ifStmt.initElse();
    m_serializer.serializeStmt(el, stmt->getElse());
  }
  return true;
}

bool StmtSerializer::VisitNullStmt(const clang::NullStmt *stmt) {
  m_builder.setNull();
  return true;
}

inline clang::SourceLocation getLoc(clang::ForStmt const *const stmt) {
  return stmt->getForLoc();
}
inline clang::SourceLocation getLoc(clang::WhileStmt const *const stmt) {
  return stmt->getWhileLoc();
}
inline clang::SourceLocation getLoc(clang::DoStmt const *const stmt) {
  return stmt->getWhileLoc();
}

template <IsLoopAstNode While>
bool StmtSerializer::serializeWhileStmt(stubs::Stmt::While::Builder builder,
                                        const While *stmt) {

  auto cond = builder.initCond();
  m_serializer.serializeExpr(cond, stmt->getCond());

  llvm::SmallVector<Annotation> anns;
  m_serializer.getAnnStore().getUntilLoc(anns, stmt->getBody()->getBeginLoc(),
                                         getSourceManager());
  auto specBuilder = builder.initSpec(anns.size());
  size_t i(0);
  for (auto &ann : anns) {
    auto annBuilder = specBuilder[i++];
    m_serializer.serializeAnnotationClause(annBuilder, ann);
  }

  auto whileLoc = builder.initWhileLoc();
  auto whileBegin = getLoc(stmt);
  serializeSourceRange(whileLoc, whileBegin, getSourceManager(),
                       getContext().getLangOpts());

  auto body = builder.initBody();
  m_serializer.serializeStmt(body, stmt->getBody());
  return true;
}

bool StmtSerializer::VisitWhileStmt(const clang::WhileStmt *stmt) {
  auto whi = m_builder.initWhile();
  return serializeWhileStmt(whi, stmt);
}

bool StmtSerializer::VisitDoStmt(const clang::DoStmt *stmt) {
  auto doWhi = m_builder.initDoWhile();
  return serializeWhileStmt(doWhi, stmt);
}

bool StmtSerializer::VisitForStmt(const clang::ForStmt *stmt) {
  using ForStmtBuilder = ::stubs::Stmt::For::Builder;
  using StmtBuilder = ::stubs::Node<stubs::Stmt>::Builder;
  using ExprBuilder = ::stubs::Node<stubs::Expr>::Builder;
  using WhileBuilder = ::stubs::Stmt::While::Builder;

  // Initialize For loop
  ForStmtBuilder forBuilder = m_builder.initFor();

  // Initialize Init of For loop [ for(init cond; iter) body; ]
  StmtBuilder initBuilder = forBuilder.initInit();
  m_serializer.serializeStmt(initBuilder, stmt->getInit());

  // Initialize Condition and Body of For loop as While
  WhileBuilder whileBuilder = forBuilder.initInsideWhile();
  if (serializeWhileStmt(whileBuilder, stmt) == 0)
    return false;

  // Initialize Iteration of For loop
  ExprBuilder iterationBuilder = forBuilder.initIteration();
  m_serializer.serializeExpr(iterationBuilder, stmt->getInc());

  return true;
}

bool StmtSerializer::VisitBreakStmt(const clang::BreakStmt *stmt) {
  m_builder.setBreak();
  return true;
}

bool StmtSerializer::VisitContinueStmt(const clang::ContinueStmt *stmt) {
  m_builder.setContinue();
  return true;
}

bool StmtSerializer::VisitSwitchStmt(const clang::SwitchStmt *stmt) {
  auto sw = m_builder.initSwitch();

  auto cond = sw.initCond();
  m_serializer.serializeExpr(cond, stmt->getCond());

  llvm::SmallVector<const clang::Stmt *, 4> casesPtrs;
  for (auto swCase = stmt->getSwitchCaseList(); swCase;
       swCase = swCase->getNextSwitchCase()) {
    casesPtrs.push_back(swCase);
  }

  auto cases = sw.initCases(casesPtrs.size());
  size_t i(casesPtrs.size());
  // clang traverses them in reverse order, so we reverse it again
  for (auto swCase : casesPtrs) {
    auto cas = cases[--i];
    m_serializer.serializeStmt(cas, swCase);
  }
  return true;
}

bool StmtSerializer::VisitCaseStmt(const clang::CaseStmt *stmt) {
  auto swCase = m_builder.initCase();

  auto lhs = swCase.initLhs();
  m_serializer.serializeExpr(lhs, stmt->getLHS());

  auto rhs = stmt->getRHS();
  // check if it has a rhs. Otherwise 'getSubsStmt' would point to the next case
  // in the switch, because that next case would be treated as a sub statement
  // in the current case statement.
  if (rhs) {
    auto subStmt = swCase.initStmt();
    m_serializer.serializeStmt(subStmt, stmt->getSubStmt());
  }
  return true;
}

bool StmtSerializer::VisitDefaultStmt(const clang::DefaultStmt *stmt) {
  auto defStmt = m_builder.initDefCase();
  auto subStmt = stmt->getSubStmt();
  if (subStmt) {
    auto sub = defStmt.initStmt();
    m_serializer.serializeStmt(sub, subStmt);
  }
  return true;
}

} // namespace vf