#include "StmtSerializer.h"
#include "Location.h"
#include "NodeListSerializer.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Lex/Token.h"

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

    m_ASTSerializer->serialize(ifStmtBuilder.initCond(), stmt->getCond());
    m_ASTSerializer->serialize(ifStmtBuilder.initThen(), stmt->getThen());

    if (stmt->hasElseStorage()) {
      m_ASTSerializer->serialize(ifStmtBuilder.initElse(), stmt->getElse());
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

  using SwitchCaseSerializers =
      std::pair<const clang::SwitchCase *, StmtListSerializer>;

  void
  serializeSwitchCases(stubs::Stmt::Switch::Builder switchBuilder,
                       llvm::MutableArrayRef<SwitchCaseSerializers> cases) {
    ListBuilder<stubs::Node<stubs::Stmt>> casesBuilder =
        switchBuilder.initCases(cases.size());
    size_t i(0);
    for (auto &[switchCase, listSerializer] : cases) {
      StmtNodeBuilder stmtBuilder = casesBuilder[i++];
      m_ASTSerializer->serialize(stmtBuilder.initLoc(),
                                 switchCase->getKeywordLoc());
      if (const clang::CaseStmt *caseStmt =
              llvm::dyn_cast<clang::CaseStmt>(switchCase)) {
        stubs::Stmt::Case::Builder caseBuilder =
            stmtBuilder.initDesc().initCase();
        m_ASTSerializer->serialize(caseBuilder.initLhs(), caseStmt->getLHS());
        listSerializer.adoptToListBuilder(
            caseBuilder.initStmts(listSerializer.size()));
        continue;
      }

      listSerializer.adoptToListBuilder(
          stmtBuilder.initDesc().initDefCase().initStmts(
              listSerializer.size()));
    }
  }

  bool VisitSwitchStmt(const clang::SwitchStmt *stmt) {
    stubs::Stmt::Switch::Builder switchBuilder = m_builder.initSwitch();
    m_ASTSerializer->serialize(switchBuilder.initCond(), stmt->getCond());

    llvm::SmallVector<SwitchCaseSerializers> cases;
    bool hasCases(false);

    // Switch body can be any statement in C++. The statement is unreachable if
    // it is not a case label or default case.
    const clang::Stmt *bodyStmt = stmt->getBody();
    if (const clang::CompoundStmt *body =
            llvm::dyn_cast<clang::CompoundStmt>(bodyStmt)) {
      for (const clang::Stmt *childStmt : body->body()) {
        // Cases are nested if they do not contain a break statement
        while (const clang::SwitchCase *switchCase =
                   llvm::dyn_cast_or_null<clang::SwitchCase>(childStmt)) {
          AnnotationsRef annotations =
              m_ASTSerializer->getAnnotationManager().getSequenceAfterLoc(
                  switchCase->getColonLoc());
          cases.emplace_back(
                   switchCase,
                   StmtListSerializer(
                       capnp::Orphanage::getForMessageContaining(m_builder),
                       StmtSerializer(*m_ASTSerializer)))
                  .second
              << annotations;
          childStmt = switchCase->getSubStmt();
        }

        if (!childStmt)
          continue;

        clang::Token nextToken =
            getNextToken(childStmt->getEndLoc(),
                         m_ASTSerializer->getASTContext().getSourceManager(),
                         m_ASTSerializer->getASTContext().getLangOpts());

        // Other statements for the same case are listed within the switch body
        cases.back().second
            << childStmt
            << m_ASTSerializer->getAnnotationManager().getSequenceAfterLoc(
                   nextToken.is(clang::tok::semi) ? nextToken.getLocation()
                                                  : childStmt->getEndLoc());
      }
      hasCases = true;
    }

    else if (const clang::SwitchCase *switchCase =
                 llvm::dyn_cast<clang::SwitchCase>(bodyStmt)) {
      cases.emplace_back(
          switchCase, StmtListSerializer(
                          capnp::Orphanage::getForMessageContaining(m_builder),
                          StmtSerializer(*m_ASTSerializer)));
      if (const clang::Stmt *subStmt = switchCase->getSubStmt()) {
        cases.back().second << subStmt;
      }
      hasCases = true;
    }

    if (hasCases) {
      serializeSwitchCases(switchBuilder, cases);
      return true;
    }

    // Body is unreachable. We serialize it as `default: break; body`
    clang::SourceRange range = getRange(stmt);
    StmtNodeBuilder stmtBuilder = switchBuilder.initCases(1)[0];
    m_ASTSerializer->serialize(stmtBuilder.initLoc(), range);
    stubs::Stmt::DefCase::Builder defCaseBuilder =
        stmtBuilder.initDesc().initDefCase();

    ListBuilder<stubs::Node<stubs::Stmt>> stmtsBuilder =
        defCaseBuilder.initStmts(2);
    stmtBuilder = stmtsBuilder[0];
    m_ASTSerializer->serialize(stmtBuilder.initLoc(), range);
    stmtBuilder.initDesc().setBreak();

    stmtBuilder = stmtsBuilder[1];

    m_ASTSerializer->serialize(stmtBuilder.initLoc(), range);
    stubs::Stmt::If::Builder ifBuilder = stmtBuilder.initDesc().initIf();

    ExprNodeBuilder condBuilder = ifBuilder.initCond();
    m_ASTSerializer->serialize(condBuilder.initLoc(), range);
    condBuilder.initDesc().setBoolLit(false);

    m_ASTSerializer->serialize(ifBuilder.initThen(), bodyStmt);

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