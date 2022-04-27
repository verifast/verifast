#include "AstSerializer.h"
#include "clang/AST/Expr.h"
#include "llvm/ADT/SmallString.h"

namespace vf {

bool ExprSerializer::VisitUnaryOperator(const clang::UnaryOperator *uo) {
  auto builder = _builder.initUnaryOp();

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
  _serializer.serializeExpr(operand, uo->getSubExpr());
  return true;
}

bool ExprSerializer::VisitBinaryOperator(const clang::BinaryOperator *bo) {
  auto builder = _builder.initBinaryOp();

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

  _serializer.serializeExpr(lhs, bo->getLHS());
  _serializer.serializeExpr(rhs, bo->getRHS());
  return true;
}

bool ExprSerializer::VisitCXXBoolLiteralExpr(
    const clang::CXXBoolLiteralExpr *expr) {
  _builder.setBoolLit(expr->getValue());
  return true;
}

bool ExprSerializer::VisitStringLiteral(const clang::StringLiteral *lit) {
  _builder.setStringLit(lit->getString().str());
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

  auto intLit = _builder.initIntLit();

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
  if (expr->getCastKind() == clang::CastKind::CK_LValueToRValue) {
    auto ce = _builder.initLValueToRValue();
    _serializer.serializeExpr(ce, expr->getSubExpr());
    return true;
  }
  if (expr->getCastKind() == clang::CastKind::CK_UncheckedDerivedToBase) {
    auto ce = _builder.initDerivedToBase();
    auto e = ce.initExpr();
    auto type = ce.initType();
    _serializer.serializeExpr(e, expr->getSubExpr());
    _serializer.serializeQualType(type, expr->getType());
    return true;
  }
  return Visit(expr->getSubExpr());
}

bool ExprSerializer::visitCall(stubs::Expr::Call::Builder &builder,
                               const clang::CallExpr *expr) {
  auto callee = builder.initCallee();
  _serializer.serializeExpr(callee, expr->getCallee());

  auto args = builder.initArgs(expr->getNumArgs());
  size_t i(0);
  for (auto *arg : expr->arguments()) {
    auto a = args[i++];
    _serializer.serializeExpr(a, arg);
  }
  return true;
}

bool ExprSerializer::VisitCallExpr(const clang::CallExpr *expr) {
  auto call = _builder.initCall();
  return visitCall(call, expr);
}

bool ExprSerializer::VisitDeclRefExpr(const clang::DeclRefExpr *expr) {
  auto declRef = _builder.initDeclRef();
  auto *decl = expr->getDecl();
  declRef.setIsClassMember(decl->isCXXClassMember());
  declRef.setName(decl->getQualifiedNameAsString());
  if (auto *func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
    declRef.setMangledName(_serializer.getMangledFunc(func).str());
  }
  return true;
}

bool ExprSerializer::VisitMemberExpr(const clang::MemberExpr *expr) {
  auto mem = _builder.initMember();

  auto base = mem.initBase();
  auto baseExpr = expr->getBase();
  _serializer.serializeExpr(base, baseExpr);

  mem.setBaseIsPointer(baseExpr->getType().getTypePtr()->isPointerType());

  auto *decl = expr->getMemberDecl();
  mem.setName(decl->getNameAsString());
  mem.setQualName(decl->getQualifiedNameAsString());
  if (auto *meth = llvm::dyn_cast<clang::CXXMethodDecl>(decl)) {
    mem.setMangledName(_serializer.getMangledFunc(meth).str());
  }
  mem.setArrow(expr->isArrow());
  return true;
}

bool ExprSerializer::VisitCXXMemberCallExpr(
    const clang::CXXMemberCallExpr *expr) {
  auto call = _builder.initMemberCall();
  return visitCall(call, expr);
}

bool ExprSerializer::VisitCXXThisExpr(const clang::CXXThisExpr *expr) {
  _builder.setThis();
  return true;
}

bool ExprSerializer::VisitCXXNewExpr(const clang::CXXNewExpr *expr) {
  auto n = _builder.initNew();

  if (expr->hasInitializer()) {
    auto e = n.initExpr();
    _serializer.serializeExpr(e, expr->getInitializer());
  }

  auto type = n.initType();
  _serializer.serializeQualType(type, expr->getAllocatedType());

  return true;
}

bool ExprSerializer::VisitCXXDeleteExpr(const clang::CXXDeleteExpr *expr) {
  auto d = _builder.initDelete();
  _serializer.serializeExpr(d, expr->getArgument());
  return true;
}

bool ExprSerializer::VisitCXXConstructExpr(
    const clang::CXXConstructExpr *expr) {
  auto construct = _builder.initConstruct();
  auto ctor = expr->getConstructor();
  construct.setName(ctor->getNameAsString());
  construct.setMangledName(_serializer.getMangledCtorName(ctor).str());
  auto args = construct.initArgs(expr->getNumArgs());

  size_t i(0);
  for (auto arg : expr->arguments()) {
    auto a = args[i++];
    _serializer.serializeExpr(a, arg);
  }

  auto type = construct.initType();
  _serializer.serializeQualType(type, expr->getType());

  return true;
}

bool ExprSerializer::VisitConstantExpr(const clang::ConstantExpr *expr) {
  return Visit(expr->getSubExpr());
}

bool ExprSerializer::VisitCXXNullPtrLiteralExpr(
    const clang::CXXNullPtrLiteralExpr *expr) {
  _builder.setNullPtrLit();
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