#include "ASTSerializer.h"
#include "DeclSerializer.h"
#include "ExprSerializer.h"
#include "Location.h"
#include "LocationSerializer.h"
#include "StmtSerializer.h"
#include "TypeSerializer.h"
#include "clang/AST/ExprConcepts.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <optional>

namespace {
void printQualifiedName(const clang::NamedDecl *decl,
                        llvm::raw_string_ostream &os,
                        const clang::PrintingPolicy &policy) {
  decl->printQualifiedName(os, policy);
}

// Collects into \p integral the indexes of the type parameters at depth
// \p depth that the constraint \p constraint requires to satisfy
// `std::integral`. Only conjuncts count: dropping a constraint can only add
// type arguments that the generic function must be verified for.
void collectIntegralTypeParams(const clang::Expr *constraint, unsigned depth,
                               llvm::SmallBitVector &integral) {
  constraint = constraint->IgnoreParens();
  if (const clang::BinaryOperator *bo =
          llvm::dyn_cast<clang::BinaryOperator>(constraint)) {
    if (bo->getOpcode() == clang::BinaryOperatorKind::BO_LAnd) {
      collectIntegralTypeParams(bo->getLHS(), depth, integral);
      collectIntegralTypeParams(bo->getRHS(), depth, integral);
    }
    return;
  }
  const clang::ConceptSpecializationExpr *concept_ =
      llvm::dyn_cast<clang::ConceptSpecializationExpr>(constraint);
  if (!concept_ ||
      concept_->getNamedConcept()->getQualifiedNameAsString() !=
          "std::integral") {
    return;
  }
  llvm::ArrayRef<clang::TemplateArgument> args =
      concept_->getTemplateArguments();
  if (args.size() != 1 || args[0].getKind() != clang::TemplateArgument::Type) {
    return;
  }
  const clang::TemplateTypeParmType *param =
      args[0].getAsType()->getAs<clang::TemplateTypeParmType>();
  if (param && param->getDepth() == depth &&
      param->getIndex() < integral.size()) {
    integral.set(param->getIndex());
  }
}

// The integral type parameters (see ASTSerializer::getIntegralTypeParams) of
// a function template.
struct IntegralTypeParams {
  const llvm::SmallBitVector &params;
  unsigned depth;

  // The index of the integral type parameter that \p type is, if any.
  std::optional<unsigned> indexOf(clang::QualType type) const {
    const clang::TemplateTypeParmType *param =
        llvm::dyn_cast<clang::TemplateTypeParmType>(
            type.getCanonicalType().getTypePtr());
    if (param && param->getDepth() == depth &&
        param->getIndex() < params.size() && params.test(param->getIndex())) {
      return param->getIndex();
    }
    return std::nullopt;
  }
};

// Whether a type in a function template can be serialized while its type
// parameters are abstract. The values of an integral type parameter are
// integers, whose addresses the verifier does not support.
bool isSupportedGenericType(clang::QualType type,
                            const IntegralTypeParams &integral,
                            bool isPointee = false) {
  if (!type->isDependentType()) {
    return true;
  }
  const clang::Type *typePtr = type.getTypePtr();
  if (const clang::TemplateTypeParmType *param =
          llvm::dyn_cast<clang::TemplateTypeParmType>(typePtr)) {
    return param->getIdentifier() && !param->isParameterPack() &&
           !(isPointee && integral.indexOf(type));
  }
  if (const clang::PointerType *pointer =
          llvm::dyn_cast<clang::PointerType>(typePtr)) {
    return isSupportedGenericType(pointer->getPointeeType(), integral, true);
  }
  if (const clang::LValueReferenceType *ref =
          llvm::dyn_cast<clang::LValueReferenceType>(typePtr)) {
    return isSupportedGenericType(ref->getPointeeType(), integral, true);
  }
  return false;
}

// Whether \p type is a builtin integer type other than bool.
bool isBuiltinIntegerType(clang::QualType type) {
  const clang::BuiltinType *builtin = llvm::dyn_cast<clang::BuiltinType>(
      type.getCanonicalType().getTypePtr());
  return builtin && builtin->isInteger() &&
         builtin->getKind() != clang::BuiltinType::Bool;
}

// What an expression of a function template is, as far as integral type
// parameters are concerned. It follows the types that the verifier gives these
// expressions.
struct IntegralExpr {
  enum Kind {
    Value,    // a value of integral type parameter `param`
    Promoted, // a value of the type that `param` is promoted to
    Literal,  // an int literal that every such type can represent
    Bool,
  } kind;
  unsigned param = 0;
};

// Checks whether a function template only uses its type parameters in ways
// that mean the same for every scalar type argument, or, for its integral type
// parameters, in ways that the verifier can verify once for every integer type
// argument other than bool. Then it can be verified once, for abstract type
// parameters. The serializers reject the same constructs when they serialize
// such a template.
class GenericFunctionChecker
    : public clang::RecursiveASTVisitor<GenericFunctionChecker> {
  const clang::FunctionDecl *m_func;
  IntegralTypeParams m_integral;
  bool m_supported = true;

  bool fail() {
    m_supported = false;
    return false;
  }

  // The operands of an arithmetic or comparison operator must be values of
  // the same integral type parameter, or small literals. Returns that type
  // parameter.
  std::optional<unsigned> getOperandsParam(const clang::Expr *lhs,
                                           const clang::Expr *rhs) const {
    std::optional<IntegralExpr> l = classifyIntegral(lhs);
    std::optional<IntegralExpr> r = classifyIntegral(rhs);
    if (!l || !r || l->kind == IntegralExpr::Bool ||
        r->kind == IntegralExpr::Bool) {
      return std::nullopt;
    }
    if (l->kind == IntegralExpr::Literal) {
      std::swap(l, r);
    }
    if (l->kind == IntegralExpr::Literal ||
        (r->kind != IntegralExpr::Literal && r->param != l->param)) {
      return std::nullopt;
    }
    return l->param;
  }

  // Classifies an expression that depends on integral type parameters.
  // Returns nothing if the verifier does not support it.
  std::optional<IntegralExpr>
  classifyIntegral(const clang::Expr *expr) const {
    expr = expr->IgnoreParens();
    if (!expr->isTypeDependent()) {
      if (expr->getType()->isBooleanType()) {
        return IntegralExpr{IntegralExpr::Bool};
      }
      // Every type argument can represent 127, and every type that a type
      // argument is promoted to can represent 32767.
      if (const clang::IntegerLiteral *lit =
              llvm::dyn_cast<clang::IntegerLiteral>(expr)) {
        if (lit->getType()->isSpecificBuiltinType(clang::BuiltinType::Int) &&
            lit->getValue().ule(32767)) {
          return IntegralExpr{IntegralExpr::Literal};
        }
      }
      return std::nullopt;
    }
    if (const clang::DeclRefExpr *ref =
            llvm::dyn_cast<clang::DeclRefExpr>(expr)) {
      if (llvm::isa<clang::VarDecl>(ref->getDecl())) {
        if (std::optional<unsigned> param =
                m_integral.indexOf(ref->getType())) {
          return IntegralExpr{IntegralExpr::Value, *param};
        }
      }
      return std::nullopt;
    }
    // The verifier checks that the value of the operand is within the limits
    // of the type argument.
    if (llvm::isa<clang::CStyleCastExpr, clang::CXXStaticCastExpr>(expr)) {
      std::optional<unsigned> param = m_integral.indexOf(expr->getType());
      const clang::Expr *operand =
          llvm::cast<clang::CastExpr>(expr)->getSubExpr();
      if (!param) {
        return std::nullopt;
      }
      if (!operand->isTypeDependent()) {
        if (isBuiltinIntegerType(operand->getType())) {
          return IntegralExpr{IntegralExpr::Value, *param};
        }
        return std::nullopt;
      }
      std::optional<IntegralExpr> kind = classifyIntegral(operand);
      if (kind && (kind->kind == IntegralExpr::Value ||
                   kind->kind == IntegralExpr::Promoted)) {
        return IntegralExpr{IntegralExpr::Value, *param};
      }
      return std::nullopt;
    }
    if (const clang::BinaryOperator *bo =
            llvm::dyn_cast<clang::BinaryOperator>(expr)) {
      switch (bo->getOpcode()) {
      case clang::BinaryOperatorKind::BO_Add:
      case clang::BinaryOperatorKind::BO_Sub:
      case clang::BinaryOperatorKind::BO_Mul:
      case clang::BinaryOperatorKind::BO_Div:
      case clang::BinaryOperatorKind::BO_Rem:
        if (std::optional<unsigned> param =
                getOperandsParam(bo->getLHS(), bo->getRHS())) {
          return IntegralExpr{IntegralExpr::Promoted, *param};
        }
        return std::nullopt;
      case clang::BinaryOperatorKind::BO_LT:
      case clang::BinaryOperatorKind::BO_GT:
      case clang::BinaryOperatorKind::BO_LE:
      case clang::BinaryOperatorKind::BO_GE:
      case clang::BinaryOperatorKind::BO_EQ:
      case clang::BinaryOperatorKind::BO_NE:
        if (getOperandsParam(bo->getLHS(), bo->getRHS())) {
          return IntegralExpr{IntegralExpr::Bool};
        }
        return std::nullopt;
      case clang::BinaryOperatorKind::BO_LAnd:
      case clang::BinaryOperatorKind::BO_LOr: {
        std::optional<IntegralExpr> l = classifyIntegral(bo->getLHS());
        std::optional<IntegralExpr> r = classifyIntegral(bo->getRHS());
        if (l && r && l->kind == IntegralExpr::Bool &&
            r->kind == IntegralExpr::Bool) {
          return IntegralExpr{IntegralExpr::Bool};
        }
        return std::nullopt;
      }
      default:
        return std::nullopt;
      }
    }
    if (const clang::UnaryOperator *uo =
            llvm::dyn_cast<clang::UnaryOperator>(expr)) {
      std::optional<IntegralExpr> operand = classifyIntegral(uo->getSubExpr());
      if (uo->getOpcode() == clang::UnaryOperatorKind::UO_LNot && operand &&
          operand->kind == IntegralExpr::Bool) {
        return IntegralExpr{IntegralExpr::Bool};
      }
      return std::nullopt;
    }
    return std::nullopt;
  }

  // A conversion to or from a type parameter depends on the type argument.
  bool checkNoConversion(clang::QualType target, clang::QualType source) {
    if (!target->isDependentType() && !source->isDependentType()) {
      return true;
    }
    if (target.getCanonicalType().getUnqualifiedType() !=
        source.getCanonicalType().getUnqualifiedType()) {
      return fail();
    }
    return true;
  }

  bool checkNoConversion(clang::QualType target, const clang::Expr *source) {
    // A comparison of values of an integral type parameter is a bool.
    if (target->isBooleanType() && source->isTypeDependent()) {
      std::optional<IntegralExpr> kind = classifyIntegral(source);
      if (kind && kind->kind == IntegralExpr::Bool) {
        return true;
      }
    }
    return checkNoConversion(target, source->getType());
  }

  bool checkCondition(const clang::Expr *cond) {
    if (!cond || !cond->isTypeDependent()) {
      return true;
    }
    std::optional<IntegralExpr> kind = classifyIntegral(cond);
    return (kind && kind->kind == IntegralExpr::Bool) || fail();
  }

public:
  GenericFunctionChecker(const clang::FunctionDecl *func,
                         IntegralTypeParams integral)
      : m_func(func), m_integral(integral) {}

  bool check() {
    if (!isSupportedGenericType(m_func->getReturnType(), m_integral)) {
      return false;
    }
    for (const clang::ParmVarDecl *param : m_func->parameters()) {
      if (!isSupportedGenericType(param->getType(), m_integral) ||
          (param->hasDefaultArg() && !param->hasUnparsedDefaultArg() &&
           !param->hasUninstantiatedDefaultArg() &&
           param->getDefaultArg()->isInstantiationDependent())) {
        return false;
      }
    }
    if (const clang::Stmt *body = m_func->getBody()) {
      TraverseStmt(const_cast<clang::Stmt *>(body));
    }
    return m_supported;
  }

  bool VisitExpr(clang::Expr *expr) {
    if (!expr->isInstantiationDependent() || classifyIntegral(expr)) {
      return true;
    }
    if (const clang::DeclRefExpr *ref = llvm::dyn_cast<clang::DeclRefExpr>(expr)) {
      return llvm::isa<clang::VarDecl>(ref->getDecl()) || fail();
    }
    if (llvm::isa<clang::ParenExpr, clang::ImplicitCastExpr,
                  clang::ConditionalOperator>(expr)) {
      return true;
    }
    if (const clang::UnaryOperator *uo =
            llvm::dyn_cast<clang::UnaryOperator>(expr)) {
      return !uo->getSubExpr()->isTypeDependent() ||
             ((uo->getOpcode() == clang::UnaryOperatorKind::UO_AddrOf ||
               uo->getOpcode() == clang::UnaryOperatorKind::UO_Deref) &&
              !m_integral.indexOf(uo->getSubExpr()->getType())) ||
             fail();
    }
    if (const clang::BinaryOperator *bo =
            llvm::dyn_cast<clang::BinaryOperator>(expr)) {
      return (!bo->getLHS()->isTypeDependent() &&
              !bo->getRHS()->isTypeDependent()) ||
             bo->getOpcode() == clang::BinaryOperatorKind::BO_Assign || fail();
    }
    // Members of type parameters, calls with type-dependent arguments, casts,
    // `sizeof(T)`, `new T`, ...
    return fail();
  }

  bool VisitBinaryOperator(clang::BinaryOperator *bo) {
    if (bo->getOpcode() != clang::BinaryOperatorKind::BO_Assign) {
      return true;
    }
    return checkNoConversion(bo->getLHS()->getType(), bo->getRHS());
  }

  bool VisitConditionalOperator(clang::ConditionalOperator *co) {
    return checkCondition(co->getCond()) &&
           checkNoConversion(co->getTrueExpr()->getType(),
                             co->getFalseExpr()->getType());
  }

  bool VisitVarDecl(clang::VarDecl *decl) {
    if (!isSupportedGenericType(decl->getType(), m_integral)) {
      return fail();
    }
    if (!decl->hasInit()) {
      return true;
    }
    if (decl->getType()->isDependentType() &&
        decl->getInitStyle() != clang::VarDecl::InitializationStyle::CInit) {
      return fail();
    }
    return checkNoConversion(decl->getType().getNonReferenceType(),
                             decl->getInit());
  }

  bool VisitReturnStmt(clang::ReturnStmt *stmt) {
    const clang::Expr *retVal = stmt->getRetValue();
    return !retVal ||
           checkNoConversion(m_func->getReturnType().getNonReferenceType(),
                             retVal);
  }

  bool VisitIfStmt(clang::IfStmt *stmt) {
    return checkCondition(stmt->getCond());
  }

  bool VisitWhileStmt(clang::WhileStmt *stmt) {
    return checkCondition(stmt->getCond());
  }

  bool VisitDoStmt(clang::DoStmt *stmt) {
    return checkCondition(stmt->getCond());
  }

  bool VisitForStmt(clang::ForStmt *stmt) {
    return checkCondition(stmt->getCond());
  }

  bool VisitSwitchStmt(clang::SwitchStmt *stmt) {
    return checkCondition(stmt->getCond());
  }
};

bool canBeVerifiedGenerically(const clang::FunctionTemplateDecl *decl,
                              const llvm::SmallBitVector &integral) {
  const clang::FunctionDecl *funcDecl = decl->getTemplatedDecl();
  if (llvm::isa<clang::CXXMethodDecl>(funcDecl)) {
    return false;
  }
  for (const clang::NamedDecl *tparam : *decl->getTemplateParameters()) {
    const clang::TemplateTypeParmDecl *typeParam =
        llvm::dyn_cast<clang::TemplateTypeParmDecl>(tparam);
    if (!typeParam || typeParam->isParameterPack() ||
        typeParam->getName().empty()) {
      return false;
    }
  }
  if (const clang::FunctionDecl *definition = funcDecl->getDefinition()) {
    funcDecl = definition;
  }
  return GenericFunctionChecker(
             funcDecl, {integral, decl->getTemplateParameters()->getDepth()})
      .check();
}
} // namespace

namespace vf {

void ASTSerializer::serialize(DeclNodeBuilder builder,
                              const clang::Decl *decl) const {
  DeclSerializer serializer(*this);
  serializer.serialize(decl, builder);
}

void ASTSerializer::serialize(StmtNodeBuilder builder,
                              const clang::Stmt *stmt) const {
  StmtSerializer serializer(*this);
  serializer.serialize(stmt, builder);
}

void ASTSerializer::serializeBody(StmtNodeBuilder builder,
                                  const clang::FunctionDecl *decl) const {
  const clang::FunctionDecl *enclosingFunction = m_currentFunction;
  m_currentFunction = decl;
  serialize(builder, decl->getBody());
  m_currentFunction = enclosingFunction;
}

void ASTSerializer::serialize(ExprNodeBuilder builder,
                              const clang::Expr *expr) const {
  ExprSerializer serializer(*this);
  serializer.serialize(expr, builder);
}

void ASTSerializer::serializeAsRValue(ExprNodeBuilder builder,
                                     const clang::Expr *expr) const {
  if (!expr->isTypeDependent() || !expr->isGLValue()) {
    serialize(builder, expr);
    return;
  }

  serialize(builder.initLoc(), getRange(expr));
  serialize(builder.initDesc().initLValueToRValue(), expr);
}

void ASTSerializer::serialize(TypeNodeBuilder builder,
                              clang::TypeLoc typeLoc) const {
  TypeLocSerializer serializer(*this);
  serializer.serialize(typeLoc, builder);
}

void ASTSerializer::serialize(stubs::Type::Builder builder,
                              clang::QualType type) const {
  TypeSerializer serializer(*this);
  serializer.serialize(type.getTypePtr(), builder);
}

void ASTSerializer::serialize(LocBuilder locBuilder,
                              clang::SourceRange range) const {
  m_locationSerializer.serialize(range, locBuilder);
}

void ASTSerializer::serialize(
    ListBuilder<stubs::Param> builder,
    llvm::ArrayRef<clang::ParmVarDecl *> params) const {
  assert(builder.size() == params.size() && "Target builder has wrong size");

  size_t i(0);
  for (const clang::ParmVarDecl *param : params) {
    stubs::Param::Builder paramBuilder = builder[i++];
    TypeNodeBuilder typeBuilder = paramBuilder.initType();

    paramBuilder.setName(param->getDeclName().getAsString());

    if (param->hasDefaultArg()) {
      ExprNodeBuilder exprBuilder = paramBuilder.initDefault();
      serialize(exprBuilder, param->getDefaultArg());
    }

    clang::TypeSourceInfo *typeSourceInfo = param->getTypeSourceInfo();
    if (typeSourceInfo) {
      serialize(typeBuilder, typeSourceInfo->getTypeLoc());
      continue;
    }

    serialize(typeBuilder.initDesc(), param->getType());
  }
}

void ASTSerializer::serialize(stubs::Clause::Builder builder,
                              const Text &text) const {
  serialize(builder.initLoc(), text.getRange());
  builder.setText(text.getText().data());
}

namespace {

template <typename T>
void serializeTextArray(ListBuilder<stubs::Clause> builder,
                        llvm::ArrayRef<T> textArray,
                        const ASTSerializer *serializer) {
  assert(builder.size() == textArray.size() && "Target builder has wrong size");

  size_t i(0);
  for (const T &text : textArray) {
    stubs::Clause::Builder annotationBuilder = builder[i++];
    serializer->serialize(annotationBuilder, text);
  }
}

} // namespace

void ASTSerializer::serialize(ListBuilder<stubs::Clause> builder,
                              llvm::ArrayRef<Text> textArray) const {
  serializeTextArray(builder, textArray, this);
}

void ASTSerializer::serialize(ListBuilder<stubs::Clause> builder,
                              llvm::ArrayRef<Annotation> annotations) const {
  serializeTextArray(builder, annotations, this);
}

std::string
ASTSerializer::getQualifiedName(const clang::NamedDecl *decl) const {
  auto it = m_nameCache.find(decl->getID());

  if (it != m_nameCache.end()) {
    return it->getSecond();
  }

  std::string s;
  llvm::raw_string_ostream os(s);
  printQualifiedName(decl, os, m_ASTContext->getPrintingPolicy());
  os.flush();

  m_nameCache.insert({decl->getID(), s});

  return s;
}

std::string
ASTSerializer::getQualifiedFuncName(const clang::FunctionDecl *decl) const {
  auto it = m_nameCache.find(decl->getID());

  if (it != m_nameCache.end()) {
    return it->getSecond();
  }

  std::string s;
  llvm::raw_string_ostream os(s);
  printQualifiedName(decl, os, m_ASTContext->getPrintingPolicy());
  os << "(";
  auto *param = decl->param_begin();
  while (param != decl->param_end()) {
    (*param)->getOriginalType().print(os, m_ASTContext->getPrintingPolicy());
    ++param;
    if (param != decl->param_end()) {
      os << ", ";
    }
  }
  os << ")";
  os.flush();

  m_nameCache.insert({decl->getID(), s});

  return s;
}

std::string ASTSerializer::getGenericFuncName(
    const clang::FunctionTemplateDecl *decl) const {
  // All redeclarations of a template must map to the same name.
  decl = decl->getCanonicalDecl();
  auto it = m_nameCache.find(decl->getID());

  if (it != m_nameCache.end()) {
    return it->getSecond();
  }

  const clang::FunctionDecl *funcDecl = decl->getTemplatedDecl();
  const clang::PrintingPolicy &policy = m_ASTContext->getPrintingPolicy();
  std::string s;
  llvm::raw_string_ostream os(s);
  printQualifiedName(funcDecl, os, policy);
  llvm::SmallBitVector integral = getIntegralTypeParams(decl);
  os << "<";
  llvm::interleave(
      llvm::enumerate(*decl->getTemplateParameters()),
      [&os, &integral](const auto &param) {
        if (integral.test(param.index())) {
          os << "std::integral ";
        }
        os << param.value()->getName();
      },
      [&os]() { os << ", "; });
  os << ">(";
  llvm::interleave(
      funcDecl->parameters(),
      [&os, &policy](const clang::ParmVarDecl *param) {
        param->getOriginalType().print(os, policy);
      },
      [&os]() { os << ", "; });
  os << ")";
  os.flush();

  m_nameCache.insert({decl->getID(), s});

  return s;
}

bool ASTSerializer::isVerifiedGenerically(
    const clang::FunctionTemplateDecl *decl) const {
  // All redeclarations of a template must agree.
  decl = decl->getCanonicalDecl();
  auto [it, inserted] = m_isVerifiedGenerically.try_emplace(decl, false);
  if (inserted) {
    std::string name = getGenericFuncName(decl);
    if (m_genericFallbacks->always.contains(name) ||
        (m_genericFallbacks->ifInstantiated.contains(name) &&
         !decl->specializations().empty())) {
      return false;
    }
    it->second = canBeVerifiedGenerically(decl, getIntegralTypeParams(decl));
  }
  return it->second;
}

llvm::SmallBitVector ASTSerializer::getIntegralTypeParams(
    const clang::FunctionTemplateDecl *decl) const {
  // All redeclarations of a template have equivalent constraints.
  decl = decl->getCanonicalDecl();
  auto [it, inserted] = m_integralTypeParams.try_emplace(decl);
  if (inserted) {
    const clang::TemplateParameterList *tparams = decl->getTemplateParameters();
    it->second.resize(tparams->size());
    llvm::SmallVector<clang::AssociatedConstraint> constraints;
    decl->getAssociatedConstraints(constraints);
    for (const clang::AssociatedConstraint &constraint : constraints) {
      collectIntegralTypeParams(constraint.ConstraintExpr, tparams->getDepth(),
                                it->second);
    }
  }
  return it->second;
}

bool ASTSerializer::hasIntegralTypeParams() const {
  const clang::FunctionTemplateDecl *decl =
      m_currentFunction ? m_currentFunction->getDescribedFunctionTemplate()
                        : nullptr;
  return decl && getIntegralTypeParams(decl).any();
}

bool ASTSerializer::isIntegralTypeParam(clang::QualType type) const {
  const clang::FunctionTemplateDecl *decl =
      m_currentFunction ? m_currentFunction->getDescribedFunctionTemplate()
                        : nullptr;
  return decl && IntegralTypeParams{getIntegralTypeParams(decl),
                                    decl->getTemplateParameters()->getDepth()}
                     .indexOf(type);
}

bool ASTSerializer::usesGenericProof(const clang::FunctionDecl *decl) const {
  if (!decl->getPrimaryTemplate() ||
      !isVerifiedGenerically(decl->getPrimaryTemplate()) ||
      decl->getTemplateSpecializationKind() !=
          clang::TSK_ImplicitInstantiation) {
    return false;
  }

  llvm::SmallBitVector integral =
      getIntegralTypeParams(decl->getPrimaryTemplate());
  for (const auto &[i, arg] : llvm::enumerate(
           decl->getTemplateSpecializationArgs()->asArray())) {
    if (arg.getKind() != clang::TemplateArgument::Type) {
      return false;
    }
    clang::QualType type = arg.getAsType().getCanonicalType();
    if (i < integral.size() && integral.test(i)) {
      if (!isBuiltinIntegerType(type)) {
        return false;
      }
    } else if (!type->isArithmeticType() && !type->isEnumeralType() &&
               !type->isPointerType()) {
      return false;
    }
  }
  return true;
}

} // namespace vf
