#include "ASTSerializer.h"
#include "DeclSerializer.h"
#include "ExprSerializer.h"
#include "Location.h"
#include "LocationSerializer.h"
#include "StmtSerializer.h"
#include "TypeSerializer.h"
#include "clang/AST/RecursiveASTVisitor.h"

namespace {
void printQualifiedName(const clang::NamedDecl *decl,
                        llvm::raw_string_ostream &os,
                        const clang::PrintingPolicy &policy) {
  decl->printQualifiedName(os, policy);
}

// Whether a type in a function template can be serialized while its type
// parameters are abstract.
bool isSupportedGenericType(clang::QualType type) {
  if (!type->isDependentType()) {
    return true;
  }
  const clang::Type *typePtr = type.getTypePtr();
  if (const clang::TemplateTypeParmType *param =
          llvm::dyn_cast<clang::TemplateTypeParmType>(typePtr)) {
    return param->getIdentifier() && !param->isParameterPack();
  }
  if (const clang::PointerType *pointer =
          llvm::dyn_cast<clang::PointerType>(typePtr)) {
    return isSupportedGenericType(pointer->getPointeeType());
  }
  if (const clang::LValueReferenceType *ref =
          llvm::dyn_cast<clang::LValueReferenceType>(typePtr)) {
    return isSupportedGenericType(ref->getPointeeType());
  }
  return false;
}

// Checks whether a function template only uses its type parameters in ways
// that mean the same for every scalar type argument. Then it can be verified
// once, for abstract type parameters. The serializers reject the same
// constructs when they serialize such a template.
class GenericFunctionChecker
    : public clang::RecursiveASTVisitor<GenericFunctionChecker> {
  const clang::FunctionDecl *m_func;
  bool m_supported = true;

  bool fail() {
    m_supported = false;
    return false;
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

  // Converting a value of a type parameter to bool depends on the type
  // argument.
  bool checkCondition(const clang::Expr *cond) {
    return !cond || !cond->isTypeDependent() || fail();
  }

public:
  explicit GenericFunctionChecker(const clang::FunctionDecl *func)
      : m_func(func) {}

  bool check() {
    if (!isSupportedGenericType(m_func->getReturnType())) {
      return false;
    }
    for (const clang::ParmVarDecl *param : m_func->parameters()) {
      if (!isSupportedGenericType(param->getType()) ||
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
    if (!expr->isInstantiationDependent()) {
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
             uo->getOpcode() == clang::UnaryOperatorKind::UO_AddrOf ||
             uo->getOpcode() == clang::UnaryOperatorKind::UO_Deref || fail();
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
    return checkNoConversion(bo->getLHS()->getType(), bo->getRHS()->getType());
  }

  bool VisitConditionalOperator(clang::ConditionalOperator *co) {
    return checkCondition(co->getCond()) &&
           checkNoConversion(co->getTrueExpr()->getType(),
                             co->getFalseExpr()->getType());
  }

  bool VisitVarDecl(clang::VarDecl *decl) {
    if (!isSupportedGenericType(decl->getType())) {
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
                             decl->getInit()->getType());
  }

  bool VisitReturnStmt(clang::ReturnStmt *stmt) {
    const clang::Expr *retVal = stmt->getRetValue();
    return !retVal ||
           checkNoConversion(m_func->getReturnType().getNonReferenceType(),
                             retVal->getType());
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

bool canBeVerifiedGenerically(const clang::FunctionTemplateDecl *decl) {
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
  return GenericFunctionChecker(funcDecl).check();
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
  os << "<";
  llvm::interleave(
      *decl->getTemplateParameters(),
      [&os](const clang::NamedDecl *param) { os << param->getName(); },
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
    it->second = canBeVerifiedGenerically(decl);
  }
  return it->second;
}

bool ASTSerializer::usesGenericProof(const clang::FunctionDecl *decl) const {
  if (!decl->getPrimaryTemplate() ||
      !isVerifiedGenerically(decl->getPrimaryTemplate()) ||
      decl->getTemplateSpecializationKind() !=
          clang::TSK_ImplicitInstantiation) {
    return false;
  }

  for (const clang::TemplateArgument &arg :
       decl->getTemplateSpecializationArgs()->asArray()) {
    if (arg.getKind() != clang::TemplateArgument::Type) {
      return false;
    }
    clang::QualType type = arg.getAsType().getCanonicalType();
    if (!type->isArithmeticType() && !type->isEnumeralType() &&
        !type->isPointerType()) {
      return false;
    }
  }
  return true;
}

} // namespace vf
