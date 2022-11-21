#include "AstSerializer.h"
#include "clang/AST/Expr.h"
#include "llvm/ADT/SmallString.h"

namespace vf {

bool ExprSerializer::VisitUnaryOperator(const clang::UnaryOperator *uo) {
  auto builder = m_builder.initUnaryOp();

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

  auto operand = builder.initOperand();
  m_serializer.serializeExpr(operand, uo->getSubExpr());
  return true;
}

bool ExprSerializer::VisitBinaryOperator(const clang::BinaryOperator *bo) {
  auto builder = m_builder.initBinaryOp();

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

  auto lhs = builder.initLhs();
  auto rhs = builder.initRhs();

  m_serializer.serializeExpr(lhs, bo->getLHS());
  m_serializer.serializeExpr(rhs, bo->getRHS());
  return true;
}

bool ExprSerializer::VisitCXXBoolLiteralExpr(
    const clang::CXXBoolLiteralExpr *expr) {
  m_builder.setBoolLit(expr->getValue());
  return true;
}

bool ExprSerializer::VisitStringLiteral(const clang::StringLiteral *lit) {
  m_builder.setStringLit(lit->getString().str());
  return true;
}

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

bool ExprSerializer::VisitIntegerLiteral(const clang::IntegerLiteral *lit) {
  llvm::SmallString<16> buffer;
  bool invalid(false);
  auto spelling =
      clang::Lexer::getSpelling(lit->getBeginLoc(), buffer, getSourceManager(),
                                getContext().getLangOpts(), &invalid);
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

  auto intLit = m_builder.initIntLit();

  intLit.setUSuffix(uSuf);

  auto lSuf = lCount == 1   ? stubs::SufKind::L_SUF
              : lCount == 2 ? stubs::SufKind::L_L_SUF
                            : stubs::SufKind::NO_SUF;
  intLit.setLSuffix(lSuf);

  auto base = spelling.startswith_insensitive("0x")  ? stubs::NbBase::HEX
              : spelling.startswith_insensitive("0") ? stubs::NbBase::OCTAL
                                                     : stubs::NbBase::DECIMAL;
  intLit.setBase(base);

  auto valStr = spelling.substr(0, spelling.size() - lCount - uSuf);
  intLit.setValue(valStr.str());
  return true;
}

bool ExprSerializer::VisitImplicitCastExpr(
    const clang::ImplicitCastExpr *expr) {
  return serializeCast(expr, false);
}

bool ExprSerializer::VisitExplicitCastExpr(
    const clang::ExplicitCastExpr *expr) {
  return serializeCast(expr, true);
}

bool ExprSerializer::serializeStructToStructCast(
    stubs::Expr::Expr::StructToStruct::Builder &builder,
    const clang::CastExpr *expr) {
  auto e = builder.initExpr();
  auto type = builder.initType();
  m_serializer.serializeExpr(e, expr->getSubExpr());
  m_serializer.serializeQualType(type, expr->getType());
  return true;
}

bool ExprSerializer::serializeCast(const clang::CastExpr *expr, bool expl) {
  switch (expr->getCastKind()) {
  case clang::CastKind::CK_LValueToRValue: {
    auto ce = m_builder.initLValueToRValue();
    m_serializer.serializeExpr(ce, expr->getSubExpr());
    return true;
  }
  case clang::CastKind::CK_UncheckedDerivedToBase:
  case clang::CastKind::CK_DerivedToBase: {
    auto ce = m_builder.initDerivedToBase();
    return serializeStructToStructCast(ce, expr);
  }
  case clang::CastKind::CK_BaseToDerived: {
    auto ce = m_builder.initBaseToDerived();
    return serializeStructToStructCast(ce, expr);
  }
  default:
    if (expl)
      return false;
    return Visit(expr->getSubExpr());
  }
}

bool ExprSerializer::serializeCall(stubs::Expr::Call::Builder &builder,
                                   const clang::CallExpr *expr) {
  auto callee = builder.initCallee();
  m_serializer.serializeExpr(callee, expr->getCallee());

  auto args = builder.initArgs(expr->getNumArgs());
  size_t i(0);
  for (auto *arg : expr->arguments()) {
    auto a = args[i++];
    m_serializer.serializeExpr(a, arg);
  }
  return true;
}

bool ExprSerializer::VisitCallExpr(const clang::CallExpr *expr) {
  auto call = m_builder.initCall();
  return serializeCall(call, expr);
}

bool ExprSerializer::VisitDeclRefExpr(const clang::DeclRefExpr *expr) {
  auto declRef = m_builder.initDeclRef();
  auto *decl = expr->getDecl();
  declRef.setName(decl->getQualifiedNameAsString());
  if (auto *func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
    declRef.setMangledName(m_serializer.getMangledFunc(func).str());
  }
  return true;
}

bool ExprSerializer::VisitMemberExpr(const clang::MemberExpr *expr) {
  auto mem = m_builder.initMember();

  auto base = mem.initBase();
  auto baseExpr = expr->getBase();
  m_serializer.serializeExpr(base, baseExpr);

  mem.setBaseIsPointer(baseExpr->getType().getTypePtr()->isPointerType());

  auto *decl = expr->getMemberDecl();
  mem.setName(decl->getNameAsString());
  mem.setQualName(decl->getQualifiedNameAsString());
  if (auto *meth = llvm::dyn_cast<clang::CXXMethodDecl>(decl)) {
    mem.setMangledName(m_serializer.getMangledFunc(meth).str());
  }
  mem.setArrow(expr->isArrow());
  return true;
}

bool ExprSerializer::VisitCXXMemberCallExpr(
    const clang::CXXMemberCallExpr *expr) {
  auto memberCall = m_builder.initMemberCall();
  memberCall.setArrow(
      expr->getImplicitObjectArgument()->getType()->isPointerType());
  auto implArg = memberCall.initImplicitArg();
  m_serializer.serializeExpr(implArg, expr->getImplicitObjectArgument());
  auto call = memberCall.initCall();
  return serializeCall(call, expr);
}

bool ExprSerializer::VisitCXXOperatorCallExpr(
    const clang::CXXOperatorCallExpr *expr) {
  auto call = m_builder.initOperatorCall();
  return serializeCall(call, expr);
}

bool ExprSerializer::VisitCXXThisExpr(const clang::CXXThisExpr *expr) {
  m_builder.setThis();
  return true;
}

bool ExprSerializer::VisitCXXNewExpr(const clang::CXXNewExpr *expr) {
  auto n = m_builder.initNew();

  if (expr->hasInitializer()) {
    auto e = n.initExpr();
    m_serializer.serializeExpr(e, expr->getInitializer());
  }

  auto type = n.initType();
  m_serializer.serializeQualType(type, expr->getAllocatedType());

  return true;
}

bool ExprSerializer::VisitCXXDeleteExpr(const clang::CXXDeleteExpr *expr) {
  auto d = m_builder.initDelete();
  m_serializer.serializeExpr(d, expr->getArgument());
  return true;
}

bool ExprSerializer::VisitCXXConstructExpr(
    const clang::CXXConstructExpr *expr) {
  auto construct = m_builder.initConstruct();
  auto ctor = expr->getConstructor();
  construct.setName(ctor->getNameAsString());
  construct.setMangledName(m_serializer.getMangledCtorName(ctor).str());
  auto args = construct.initArgs(expr->getNumArgs());

  size_t i(0);
  for (auto arg : expr->arguments()) {
    auto a = args[i++];
    m_serializer.serializeExpr(a, arg);
  }

  auto type = construct.initType();
  m_serializer.serializeQualType(type, expr->getType());

  return true;
}

bool ExprSerializer::VisitConstantExpr(const clang::ConstantExpr *expr) {
  return Visit(expr->getSubExpr());
}

bool ExprSerializer::VisitCXXNullPtrLiteralExpr(
    const clang::CXXNullPtrLiteralExpr *expr) {
  m_builder.setNullPtrLit();
  return true;
}

bool ExprSerializer::VisitParenExpr(const clang::ParenExpr *expr) {
  return Visit(expr->getSubExpr());
}

bool ExprSerializer::VisitCXXDefaultInitExpr(
    const clang::CXXDefaultInitExpr *expr) {
  return Visit(expr->getExpr());
}

} // namespace vf