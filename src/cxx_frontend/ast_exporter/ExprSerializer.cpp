#include "ExprSerializer.h"
#include "Location.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Lex/Lexer.h"

namespace vf {

namespace {

bool checkSuffixIgnoreCase(const clang::StringRef str, const char suffix,
                           size_t &offset) {
  auto strSize = str.size() - offset;
  if (strSize < 1)
    return false;
  if (tolower(*(str.end() - 1 - offset)) == tolower(suffix)) {
    ++offset;
    return true;
  }
  return false;
}

struct ExprSerializerImpl
    : public clang::ConstStmtVisitor<ExprSerializerImpl, bool> {

  bool serializeCast(const clang::CastExpr *expr, bool isExplicit) {
    switch (expr->getCastKind()) {
    case clang::CastKind::CK_LValueToRValue: {
      ExprNodeBuilder ce = m_builder.initLValueToRValue();
      m_ASTSerializer->serialize(ce, expr->getSubExpr());
      return true;
    }
    case clang::CastKind::CK_UncheckedDerivedToBase:
    case clang::CastKind::CK_DerivedToBase: {
      stubs::Expr::Cast::Builder ce = m_builder.initDerivedToBase();
      return serializeCast(ce, expr);
    }
    case clang::CastKind::CK_BaseToDerived: {
      stubs::Expr::Cast::Builder ce = m_builder.initBaseToDerived();
      return serializeCast(ce, expr);
    }
    case clang::CastKind::CK_NoOp: // Required for down-casts of integral types
    case clang::CastKind::CK_IntegralCast: {
      if (isExplicit) {
        stubs::Expr::Cast::Builder ce = m_builder.initIntegralCast();
        return serializeCast(ce, expr);
      } else {
        serialize(expr->getSubExpr());
        return true;
      }
    }
    case clang::CastKind::CK_PointerToIntegral: {
      stubs::Expr::Cast::Builder ce = m_builder.initIntegralCast();
      return serializeCast(ce, expr);
    }
    default:
      if (isExplicit)
        return false;
      serialize(expr->getSubExpr());
      return true;
    }
  }

  bool VisitUnaryOperator(const clang::UnaryOperator *uo) {
    stubs::Expr::UnaryOp::Builder builder = m_builder.initUnaryOp();

#define CASE_OP(CLANG_OP, STUBS_OP)                                            \
  case clang::UnaryOperatorKind::UO_##CLANG_OP:                                \
    builder.setKind(stubs::UnaryOpKind::STUBS_OP);                             \
    break;

    switch (uo->getOpcode()) {
      CASE_OP(Minus, MINUS)
      CASE_OP(Plus, PLUS)
      CASE_OP(Not, NOT)
      CASE_OP(LNot, L_NOT)
      CASE_OP(AddrOf, ADDR_OF)
      CASE_OP(Deref, DEREF)
      CASE_OP(PreInc, PRE_INC)
      CASE_OP(PreDec, PRE_DEC)
      CASE_OP(PostInc, POST_INC)
      CASE_OP(PostDec, POST_DEC)
    default:
      return false;
    }

#undef CASE_OP

    ExprNodeBuilder operandBuilder = builder.initOperand();
    m_ASTSerializer->serialize(operandBuilder, uo->getSubExpr());
    return true;
  }

  bool VisitBinaryOperator(const clang::BinaryOperator *bo) {
    stubs::Expr::BinaryOp::Builder builder = m_builder.initBinaryOp();

#define CASE_OP(CLANG_OP, STUBS_OP)                                            \
  case clang::BinaryOperatorKind::BO_##CLANG_OP:                               \
    builder.setKind(stubs::BinaryOpKind::STUBS_OP);                            \
    break;

    switch (bo->getOpcode()) {
      CASE_OP(Assign, ASSIGN)
      CASE_OP(Add, ADD)
      CASE_OP(Sub, SUB)
      CASE_OP(Mul, MUL)
      CASE_OP(Div, DIV)
      CASE_OP(Rem, REM)
      CASE_OP(Shl, SHL)
      CASE_OP(Shr, SHR)
      CASE_OP(LT, LT)
      CASE_OP(GT, GT)
      CASE_OP(LE, LE)
      CASE_OP(GE, GE)
      CASE_OP(EQ, EQ)
      CASE_OP(NE, NE)
      CASE_OP(And, AND)
      CASE_OP(Or, OR)
      CASE_OP(Xor, XOR)
      CASE_OP(LAnd, L_AND)
      CASE_OP(LOr, L_OR)
      CASE_OP(MulAssign, MUL_ASSIGN)
      CASE_OP(DivAssign, DIV_ASSIGN)
      CASE_OP(RemAssign, REM_ASSIGN)
      CASE_OP(AddAssign, ADD_ASSIGN)
      CASE_OP(SubAssign, SUB_ASSIGN)
      CASE_OP(ShlAssign, SHL_ASSIGN)
      CASE_OP(ShrAssign, SHR_ASSIGN)
      CASE_OP(AndAssign, AND_ASSIGN)
      CASE_OP(XorAssign, XOR_ASSIGN)
      CASE_OP(OrAssign, OR_ASSIGN)
    default:
      return false;
    }

#undef CASE_OP

    ExprNodeBuilder lhsBuilder = builder.initLhs();
    ExprNodeBuilder rhsBuilder = builder.initRhs();

    m_ASTSerializer->serialize(lhsBuilder, bo->getLHS());
    m_ASTSerializer->serialize(rhsBuilder, bo->getRHS());
    return true;
  }

  bool VisitConditionalOperator(clang::ConditionalOperator const *const co) {
    using CondOpBuilder = stubs::Expr::ConditionalOp::Builder;
    using ExprBuilder = stubs::Node<stubs::Expr>::Builder;

    // Initialize Cap'n Proto elements
    CondOpBuilder condOpBuilder = m_builder.initConditionalOp();

    ExprBuilder condExpr = condOpBuilder.initCond();
    ExprBuilder thenExpr = condOpBuilder.initThen();
    ExprBuilder elseExpr = condOpBuilder.initElse();

    // Serialize subexpressions
    m_ASTSerializer->serialize(condExpr, co->getCond());
    m_ASTSerializer->serialize(thenExpr, co->getTrueExpr());
    m_ASTSerializer->serialize(elseExpr, co->getFalseExpr());

    return true;
  }

  bool VisitCXXBoolLiteralExpr(const clang::CXXBoolLiteralExpr *expr) {
    m_builder.setBoolLit(expr->getValue());
    return true;
  }

  bool VisitStringLiteral(const clang::StringLiteral *lit) {
    m_builder.setStringLit(lit->getString().str());
    return true;
  }

  bool VisitCharacterLiteral(clang::CharacterLiteral const *const lit) {
    using CharKind = clang::CharacterLiteral::CharacterKind;
    // Check if encoding is UTF16 or UTF32 as their types are defined unsigned
    // according to C++ standard
    CharKind const kind = lit->getKind();
    bool const uSuf = (kind == CharKind::UTF16 || kind == CharKind::UTF32);

    // Initialize IntLit
    ::stubs::Expr::IntLit::Builder intLit = m_builder.initIntLit();
    intLit.setUSuffix(uSuf);
    intLit.setLSuffix(stubs::SufKind::NO_SUF);
    intLit.setBase(stubs::NbBase::CHARACTER);
    // Ensure that the value always fits into a single uint64_t
    static_assert(sizeof(lit->getValue()) < 8);
    intLit.setLowBits(lit->getValue());
    intLit.setHighBits(0);

    return true;
  }

  bool VisitIntegerLiteral(const clang::IntegerLiteral *lit) {
    llvm::SmallString<16> buffer;
    bool invalid(false);
    auto spelling = clang::Lexer::getSpelling(
        m_ASTSerializer->getASTContext().getSourceManager().getSpellingLoc(
            lit->getBeginLoc()),
        buffer, m_ASTSerializer->getASTContext().getSourceManager(),
        m_ASTSerializer->getASTContext().getLangOpts(), &invalid);
    assert(!invalid);

    size_t offset(0);
    bool uSuf(checkSuffixIgnoreCase(spelling, 'u', offset));

    unsigned lCount(0);
    for (unsigned i(0); i < 2; ++i) {
      if (checkSuffixIgnoreCase(spelling, 'l', offset))
        ++lCount;
    }

    if (!uSuf && lCount > 0) {
      uSuf = checkSuffixIgnoreCase(spelling, 'u', offset);
    }

    stubs::Expr::IntLit::Builder intLitBuilder = m_builder.initIntLit();

    intLitBuilder.setUSuffix(uSuf);

    stubs::SufKind lSuf = lCount == 1   ? stubs::SufKind::L_SUF
                          : lCount == 2 ? stubs::SufKind::L_L_SUF
                                        : stubs::SufKind::NO_SUF;
    intLitBuilder.setLSuffix(lSuf);

    stubs::NbBase base =
        spelling.startswith_insensitive("0x")  ? stubs::NbBase::HEX
        : spelling.startswith_insensitive("0") ? stubs::NbBase::OCTAL
                                               : stubs::NbBase::DECIMAL;
    intLitBuilder.setBase(base);

    llvm::APInt const val = lit->getValue();

    assert(val.getNumWords() <= 2);
    if (val.getNumWords() >= 2)
      intLitBuilder.setHighBits(val.getRawData()[1]);
    if (val.getNumWords() >= 1)
      intLitBuilder.setLowBits(val.getRawData()[0]);

    return true;
  }

  bool serializeCast(stubs::Expr::Cast::Builder &builder,
                     const clang::CastExpr *expr) {
    ExprNodeBuilder exprBuilder = builder.initExpr();
    stubs::Type::Builder typeBuilder = builder.initType();
    m_ASTSerializer->serialize(exprBuilder, expr->getSubExpr());
    m_ASTSerializer->serialize(typeBuilder, expr->getType());
    return true;
  }

  bool VisitImplicitCastExpr(const clang::ImplicitCastExpr *expr) {
    return serializeCast(expr, false);
  }

  bool VisitExplicitCastExpr(const clang::ExplicitCastExpr *expr) {
    return serializeCast(expr, true);
  }

  bool serializeCall(stubs::Expr::Call::Builder &builder,
                     const clang::CallExpr *expr) {
    ExprNodeBuilder calleeBuilder = builder.initCallee();
    m_ASTSerializer->serialize(calleeBuilder, expr->getCallee());

    ListBuilder<stubs::Node<stubs::Expr>> argsBuilder =
        builder.initArgs(expr->getNumArgs());
    size_t i(0);
    for (const clang::Expr *arg : expr->arguments()) {
      ExprNodeBuilder a = argsBuilder[i++];
      m_ASTSerializer->serialize(a, arg);
    }
    return true;
  }

  bool VisitCallExpr(const clang::CallExpr *expr) {
    stubs::Expr::Call::Builder callBuilder = m_builder.initCall();
    return serializeCall(callBuilder, expr);
  }

  bool VisitDeclRefExpr(const clang::DeclRefExpr *expr) {
    const clang::NamedDecl *decl = expr->getDecl();
    if (const clang::FunctionDecl *func =
            llvm::dyn_cast<clang::FunctionDecl>(decl)) {
      m_builder.setDeclRef(m_ASTSerializer->getQualifiedFuncName(func));
      return true;
    }
    m_builder.setDeclRef(m_ASTSerializer->getQualifiedName(decl));
    return true;
  }

  bool VisitMemberExpr(const clang::MemberExpr *expr) {
    stubs::Expr::Member::Builder memberBuilder = m_builder.initMember();

    ExprNodeBuilder baseBuilder = memberBuilder.initBase();
    const clang::Expr *baseExpr = expr->getBase();
    m_ASTSerializer->serialize(baseBuilder, baseExpr);

    memberBuilder.setBaseIsPointer(
        baseExpr->getType().getTypePtr()->isPointerType());

    const clang::ValueDecl *decl = expr->getMemberDecl();
    memberBuilder.setArrow(expr->isArrow());
    if (const clang::CXXMethodDecl *meth =
            llvm::dyn_cast<clang::CXXMethodDecl>(decl)) {
      memberBuilder.setName(m_ASTSerializer->getQualifiedFuncName(meth));
      return true;
    }
    memberBuilder.setName(decl->getNameAsString());
    return true;
  }

  bool VisitCXXMemberCallExpr(const clang::CXXMemberCallExpr *expr) {
    stubs::Expr::MemberCall::Builder memberCallBuilder =
        m_builder.initMemberCall();
    memberCallBuilder.setArrow(
        expr->getImplicitObjectArgument()->getType()->isPointerType());
    ExprNodeBuilder implArg = memberCallBuilder.initImplicitArg();
    m_ASTSerializer->serialize(implArg, expr->getImplicitObjectArgument());
    stubs::Expr::Call::Builder call = memberCallBuilder.initCall();

    if (const clang::MemberExpr *callee =
            llvm::dyn_cast<clang::MemberExpr>(expr->getCallee())) {
      memberCallBuilder.setTargetHasQualifier(callee->hasQualifier());
    }

    return serializeCall(call, expr);
  }

  bool VisitCXXOperatorCallExpr(const clang::CXXOperatorCallExpr *expr) {
    stubs::Expr::Call::Builder callBuilder = m_builder.initOperatorCall();
    return serializeCall(callBuilder, expr);
  }

  bool VisitCXXDefaultArgExpr(const clang::CXXDefaultArgExpr * expr) {
    serialize(expr->getExpr());
    return true;
  }

  bool VisitCXXThisExpr(const clang::CXXThisExpr *expr) {
    m_builder.setThis();
    return true;
  }

  bool VisitCXXNewExpr(const clang::CXXNewExpr *expr) {
    stubs::Expr::New::Builder newBuilder = m_builder.initNew();

    if (expr->hasInitializer()) {
      ExprNodeBuilder exprBuilder = newBuilder.initExpr();
      m_ASTSerializer->serialize(exprBuilder, expr->getInitializer());
    }

    stubs::Type::Builder type = newBuilder.initType();
    m_ASTSerializer->serialize(type, expr->getAllocatedType());

    return true;
  }

  bool VisitCXXDeleteExpr(const clang::CXXDeleteExpr *expr) {
    ExprNodeBuilder deleteBuilder = m_builder.initDelete();
    m_ASTSerializer->serialize(deleteBuilder, expr->getArgument());
    return true;
  }

  bool VisitCXXConstructExpr(const clang::CXXConstructExpr *expr) {
    stubs::Expr::Construct::Builder constructBuilder =
        m_builder.initConstruct();
    const clang::CXXConstructorDecl *ctor = expr->getConstructor();
    constructBuilder.setName(m_ASTSerializer->getQualifiedFuncName(ctor));
    ListBuilder<stubs::Node<stubs::Expr>> args =
        constructBuilder.initArgs(expr->getNumArgs());

    size_t i(0);
    for (const clang::Expr *arg : expr->arguments()) {
      ExprNodeBuilder a = args[i++];
      m_ASTSerializer->serialize(a, arg);
    }

    stubs::Type::Builder type = constructBuilder.initType();
    m_ASTSerializer->serialize(type, expr->getType());

    return true;
  }

  bool VisitConstantExpr(const clang::ConstantExpr *expr) {
    serialize(expr->getSubExpr());
    return true;
  }

  bool VisitCXXNullPtrLiteralExpr(const clang::CXXNullPtrLiteralExpr *expr) {
    m_builder.setNullPtrLit();
    return true;
  }

  bool VisitParenExpr(const clang::ParenExpr *expr) {
    serialize(expr->getSubExpr());
    return true;
  }

  bool VisitCXXDefaultInitExpr(const clang::CXXDefaultInitExpr *expr) {
    serialize(expr->getExpr());
    return true;
  }

  bool VisitExprWithCleanups(const clang::ExprWithCleanups *expr) {
    ExprNodeBuilder cleanupsBuilder = m_builder.initCleanups();
    m_ASTSerializer->serialize(cleanupsBuilder, expr->getSubExpr());
    return true;
  }

  bool VisitCXXBindTemporaryExpr(const clang::CXXBindTemporaryExpr *expr) {
    ExprNodeBuilder tempBuilder = m_builder.initBindTemporary();
    m_ASTSerializer->serialize(tempBuilder, expr->getSubExpr());
    return true;
  }

  bool VisitMaterializeTemporaryExpr(clang::MaterializeTemporaryExpr const * expr) {
    ExprNodeBuilder tempBuilder = m_builder.initMaterializeTemporary();
    m_ASTSerializer->serialize(tempBuilder, expr->getSubExpr());
    return true;
  }

  void serialize(const clang::Expr *expr) {
    const Annotation *truncatingOpt =
        m_ASTSerializer->getAnnotationManager().getTruncating(expr);
    if (truncatingOpt) {
      ExprNodeBuilder exprBuilder = m_builder.initTruncating();
      m_ASTSerializer->serialize(exprBuilder.initLoc(),
                                 truncatingOpt->getRange());
      m_builder = exprBuilder.initDesc();
    }

    if (Visit(expr)) {
      return;
    }

    clang::DiagnosticsEngine &diagsEngine =
        m_ASTSerializer->getASTContext().getDiagnostics();
    unsigned diagID =
        diagsEngine.getCustomDiagID(clang::DiagnosticsEngine::Error,
                                    "Expression of kind '%0' is not supported");
    diagsEngine.Report(expr->getBeginLoc(), diagID) << expr->getStmtClassName();
  }

  ExprSerializerImpl(const ASTSerializer &serializer,
                     stubs::Expr::Builder builder)
      : m_builder(builder), m_ASTSerializer(&serializer) {}

  stubs::Expr::Builder m_builder;
  const ASTSerializer *m_ASTSerializer;
};

} // namespace

void ExprSerializer::serialize(const clang::Expr *expr,
                               stubs::Loc::Builder locBuilder,
                               stubs::Expr::Builder exprBuilder) const {
  assert(expr && "Expression should not be null");

  clang::SourceRange range = getRange(expr);
  ExprSerializerImpl serializer(*m_ASTSerializer, exprBuilder);
  serializer.serialize(expr);
  m_ASTSerializer->serialize(locBuilder, range);
}

} // namespace vf