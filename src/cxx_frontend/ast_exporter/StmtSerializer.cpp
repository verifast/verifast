#include "StmtSerializer.h"
#include "Location.h"
#include "NodeListSerializer.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Basic/Diagnostic.h"

namespace vf {

namespace {

struct StmtSerializerImpl
    : public clang::ConstStmtVisitor<StmtSerializerImpl, bool> {

  bool VisitCompoundStmt(const clang::CompoundStmt *stmt) {
    StmtListSerializer stmtListSerializer(
        capnp::Orphanage::getForMessageContaining(m_builder),
        StmtSerializer(*m_ASTSerializer));

    clang::SourceLocation beginLoc = stmt->getLBracLoc();
    for (const clang::Stmt *childStmt : stmt->body()) {
      AnnotationsRef annotations =
          m_ASTSerializer->getAnnotationManager().getInRange(
              beginLoc, childStmt->getBeginLoc());
      stmtListSerializer << annotations << childStmt;
      beginLoc = childStmt->getEndLoc();
    }

    AnnotationsRef annotations =
        m_ASTSerializer->getAnnotationManager().getInRange(beginLoc,
                                                           stmt->getRBracLoc());
    stmtListSerializer << annotations;

    stubs::Stmt::Compound::Builder compoundBuilder = m_builder.initCompound();
    ListBuilder<stubs::Node<stubs::Stmt>> children =
        compoundBuilder.initStmts(stmtListSerializer.size());
    stmtListSerializer.adoptToListBuilder(children);

    LocBuilder rBraceLocBuilder = compoundBuilder.initRBrace();
    auto rBraceLoc = stmt->getRBracLoc();
    m_ASTSerializer->serialize(rBraceLocBuilder, stmt->getRBracLoc());

    return true;
  }

  bool VisitReturnStmt(const clang::ReturnStmt *stmt) {
    stubs::Stmt::Return::Builder returnBuilder = m_builder.initReturn();
    const clang::Expr *retVal = stmt->getRetValue();

    if (retVal) {
      ExprNodeBuilder retExprBuilder = returnBuilder.initExpr();
      m_ASTSerializer->serialize(retExprBuilder, retVal);
    }
    return true;
  }

  bool VisitDeclStmt(const clang::DeclStmt *stmt) {
    auto nbChildren = std::distance(stmt->decl_begin(), stmt->decl_end());
    ListBuilder<stubs::Node<stubs::Decl>> children =
        m_builder.initDecl(nbChildren);

    size_t i(0);
    for (auto it = stmt->decl_begin(); it != stmt->decl_end(); ++it, ++i) {
      DeclNodeBuilder childBuilder = children[i];
      m_ASTSerializer->serialize(childBuilder, *it);
    }
    return true;
  }

  bool VisitExpr(const clang::Expr *stmt) {
    ExprNodeBuilder exprBuilder = m_builder.initExpr();
    m_ASTSerializer->serialize(exprBuilder, stmt);
    return true;
  }

  bool VisitIfStmt(const clang::IfStmt *stmt) {
    stubs::Stmt::If::Builder ifStmtBuilder = m_builder.initIf();

    ExprNodeBuilder condBuilder = ifStmtBuilder.initCond();
    m_ASTSerializer->serialize(condBuilder, stmt->getCond());

    StmtNodeBuilder then = ifStmtBuilder.initThen();
    m_ASTSerializer->serialize(then, stmt->getThen());

    if (stmt->hasElseStorage()) {
      StmtNodeBuilder elseBuilder = ifStmtBuilder.initElse();
      m_ASTSerializer->serialize(elseBuilder, stmt->getElse());
    }
    return true;
  }

  bool VisitNullStmt(const clang::NullStmt *stmt) {
    m_builder.setNull();
    return true;
  }

  template <typename While>
  bool serializeWhileStmt(stubs::Stmt::While::Builder builder,
                          const While *stmt, clang::SourceLocation whileLoc,
                          clang::SourceLocation contractStartLoc) {

    ExprNodeBuilder condBuilder = builder.initCond();
    m_ASTSerializer->serialize(condBuilder, stmt->getCond());

    AnnotationsRef contract =
        m_ASTSerializer->getAnnotationManager().getInRange(
            contractStartLoc, stmt->getBody()->getBeginLoc());
    ListBuilder<stubs::Clause> contractBuilder =
        builder.initSpec(contract.size());
    m_ASTSerializer->serialize(contractBuilder, contract);

    LocBuilder whileLocBuilder = builder.initWhileLoc();
    m_ASTSerializer->serialize(whileLocBuilder, whileLoc);

    StmtNodeBuilder bodyBuilder = builder.initBody();
    m_ASTSerializer->serialize(bodyBuilder, stmt->getBody());
    return true;
  }

  bool VisitWhileStmt(const clang::WhileStmt *stmt) {
    stubs::Stmt::While::Builder whileBuilder = m_builder.initWhile();
    return serializeWhileStmt(whileBuilder, stmt, stmt->getWhileLoc(),
                              stmt->getRParenLoc());
  }

  bool VisitDoStmt(const clang::DoStmt *stmt) {
    stubs::Stmt::While::Builder doWhileBuilder = m_builder.initDoWhile();
    return serializeWhileStmt(doWhileBuilder, stmt, stmt->getWhileLoc(),
                              stmt->getDoLoc());
  }

  bool VisitForStmt(const clang::ForStmt *stmt) {
    using ForStmtBuilder = ::stubs::Stmt::For::Builder;
    using StmtBuilder = ::stubs::Node<stubs::Stmt>::Builder;
    using ExprBuilder = ::stubs::Node<stubs::Expr>::Builder;
    using WhileBuilder = ::stubs::Stmt::While::Builder;

    // Initialize For loop
    ForStmtBuilder forBuilder = m_builder.initFor();

    // Initialize Init of For loop [ for(init cond; iter) body; ]
    StmtBuilder initBuilder = forBuilder.initInit();
    m_ASTSerializer->serialize(initBuilder, stmt->getInit());

    // Initialize Condition and Body of For loop as While
    WhileBuilder whileBuilder = forBuilder.initInsideWhile();
    if (!serializeWhileStmt(whileBuilder, stmt, stmt->getForLoc(),
                            stmt->getRParenLoc())) {
      return false;
    }

    // Initialize Iteration of For loop
    ExprBuilder iterationBuilder = forBuilder.initIteration();
    m_ASTSerializer->serialize(iterationBuilder, stmt->getInc());

    return true;
  }

  bool VisitBreakStmt(const clang::BreakStmt *stmt) {
    m_builder.setBreak();
    return true;
  }

  bool VisitContinueStmt(const clang::ContinueStmt *stmt) {
    m_builder.setContinue();
    return true;
  }

  bool VisitSwitchStmt(const clang::SwitchStmt *stmt) {
    stubs::Stmt::Switch::Builder switchBuilder = m_builder.initSwitch();

    ExprNodeBuilder condBuilder = switchBuilder.initCond();
    m_ASTSerializer->serialize(condBuilder, stmt->getCond());

    llvm::SmallVector<const clang::Stmt *> casesPtrs;
    for (const clang::SwitchCase *swCase = stmt->getSwitchCaseList(); swCase;
         swCase = swCase->getNextSwitchCase()) {
      casesPtrs.push_back(swCase);
    }

    ListBuilder<stubs::Node<stubs::Stmt>> casesBuilder =
        switchBuilder.initCases(casesPtrs.size());
    size_t i(casesPtrs.size());
    // clang traverses them in reverse order, so we reverse it again
    for (const clang::Stmt *swCase : casesPtrs) {
      StmtNodeBuilder caseBuilder = casesBuilder[--i];
      m_ASTSerializer->serialize(caseBuilder, swCase);
    }
    return true;
  }

  bool VisitCaseStmt(const clang::CaseStmt *stmt) {
    stubs::Stmt::Case::Builder swCaseBuilder = m_builder.initCase();

    ExprNodeBuilder lhsBuilder = swCaseBuilder.initLhs();
    m_ASTSerializer->serialize(lhsBuilder, stmt->getLHS());

    const clang::Expr *rhs = stmt->getRHS();
    // check if it has a rhs. Otherwise 'getSubsStmt' would point to the next
    // case in the switch, because that next case would be treated as a sub
    // statement in the current case statement.
    if (rhs) {
      StmtNodeBuilder subStmt = swCaseBuilder.initStmt();
      m_ASTSerializer->serialize(subStmt, stmt->getSubStmt());
    }
    return true;
  }

  bool VisitDefaultStmt(const clang::DefaultStmt *stmt) {
    stubs::Stmt::DefCase::Builder defStmtBuilder = m_builder.initDefCase();
    const clang::Stmt *subStmt = stmt->getSubStmt();
    if (subStmt) {
      StmtNodeBuilder sub = defStmtBuilder.initStmt();
      m_ASTSerializer->serialize(sub, subStmt);
    }
    return true;
  }

  bool serialize(const clang::Stmt *stmt) {
    if (Visit(stmt)) {
      return true;
    }

    clang::DiagnosticsEngine &diagsEngine =
        m_ASTSerializer->getASTContext().getDiagnostics();
    unsigned diagID =
        diagsEngine.getCustomDiagID(clang::DiagnosticsEngine::Error,
                                    "Statement of kind '%0' is not supported");
    diagsEngine.Report(stmt->getBeginLoc(), diagID) << stmt->getStmtClassName();

    return false;
  }

  StmtSerializerImpl(const ASTSerializer &serializer,
                     stubs::Stmt::Builder builder)
      : m_builder(builder), m_ASTSerializer(&serializer) {}

  stubs::Stmt::Builder m_builder;
  const ASTSerializer *m_ASTSerializer;
};

} // namespace

void StmtSerializer::serialize(const clang::Stmt *stmt,
                               stubs::Loc::Builder locBuilder,
                               stubs::Stmt::Builder stmtBuilder) const {
  assert(stmt && "Statement should not be null");

  clang::SourceRange range = getRange(stmt);
  StmtSerializerImpl serializer(*m_ASTSerializer, stmtBuilder);
  serializer.serialize(stmt);
  m_ASTSerializer->serialize(locBuilder, range);
}

void StmtSerializer::serialize(const Annotation &annotation,
                               stubs::Loc::Builder locBuilder,
                               stubs::Stmt::Builder stmtBuilder) const {
  clang::SourceRange range = annotation.getRange();
  m_ASTSerializer->serialize(locBuilder, range);
  stmtBuilder.setAnn(annotation.getText().data());
}

} // namespace vf