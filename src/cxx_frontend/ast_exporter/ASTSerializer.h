#pragma once

#include "AnnotationManager.h"
#include "LocationSerializer.h"
#include "stubs_ast.capnp.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"
#include "clang/AST/TypeLoc.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/StringSet.h"

namespace vf {

/**
 * @brief Function templates whose generic function failed to verify in an
 * earlier run of VeriFast, by generic function name (see
 * ASTSerializer::getGenericFuncName). Their specializations are verified
 * separately instead.
 */
struct GenericFallbacks {
  /**
   * @brief Templates whose generic function failed to type-check. They are
   * verified per specialization, and not at all if nothing instantiates them.
   */
  llvm::StringSet<> always;

  /**
   * @brief Templates whose generic function failed to verify. They are
   * verified per specialization if something instantiates them. Otherwise,
   * the generic function is still verified, so that the failure is reported.
   */
  llvm::StringSet<> ifInstantiated;
};

/**
 * @brief Serializer for various nodes in the AST of a translation unit.
 *
 */
class ASTSerializer {
public:
  void serialize(DeclNodeBuilder builder, const clang::Decl *decl) const;

  void serialize(StmtNodeBuilder builder, const clang::Stmt *stmt) const;

  /**
   * @brief Serialize the body of the function definition \p decl.
   */
  void serializeBody(StmtNodeBuilder builder,
                     const clang::FunctionDecl *decl) const;

  /**
   * @brief Function whose body is being serialized, or null.
   */
  const clang::FunctionDecl *getCurrentFunction() const {
    return m_currentFunction;
  }

  void serialize(ExprNodeBuilder builder, const clang::Expr *expr) const;

  /**
   * @brief Serialize an expression that is used as a prvalue.
   *
   * Clang does not insert an lvalue-to-rvalue conversion for an expression
   * whose type depends on a template parameter. Function templates are
   * verified once for abstract scalar type parameters, and for a scalar type
   * Clang would have inserted that conversion. So we insert it here.
   */
  void serializeAsRValue(ExprNodeBuilder builder,
                         const clang::Expr *expr) const;

  void serialize(TypeNodeBuilder builder, clang::TypeLoc typeLoc) const;

  void serialize(stubs::Type::Builder builder, clang::QualType type) const;

  void serialize(ListBuilder<stubs::Param> builder,
                 llvm::ArrayRef<clang::ParmVarDecl *> params) const;

  void serialize(stubs::Clause::Builder builder, const Text &text) const;

  void serialize(ListBuilder<stubs::Clause> builder,
                 llvm::ArrayRef<Text> textArray) const;

  void serialize(ListBuilder<stubs::Clause> builder,
                 llvm::ArrayRef<Annotation> annotations) const;

  void serialize(stubs::Loc::Builder locBuilder,
                 clang::SourceRange range) const;

  std::string getQualifiedName(const clang::NamedDecl *decl) const;

  std::string getQualifiedFuncName(const clang::FunctionDecl *decl) const;

  /**
   * @brief Name of the generic function that a function template is
   * translated to, e.g. `identity<T>(const T)` or
   * `inc<std::integral T>(const T)`.
   */
  std::string
  getGenericFuncName(const clang::FunctionTemplateDecl *decl) const;

  /**
   * @brief Whether the function template \p decl is translated to a generic
   * function, which is verified once for abstract type parameters.
   *
   * This is the case if its body only uses its type parameters in ways that
   * mean the same for every scalar type argument, or, for a type parameter
   * that is constrained by `std::integral`, for every integer type argument
   * other than bool, and its generic function did not fail in an earlier run
   * (see GenericFallbacks). Otherwise, each of its specializations is verified
   * separately.
   */
  bool isVerifiedGenerically(const clang::FunctionTemplateDecl *decl) const;

  /**
   * @brief The type parameters of the function template \p decl that its
   * constraints require to satisfy `std::integral`, by index.
   *
   * In the generic function, the values of such a type parameter are
   * integers within limits that are unknown, but that hold for every integer
   * type other than bool. So arithmetic on them can be verified once.
   */
  llvm::SmallBitVector
  getIntegralTypeParams(const clang::FunctionTemplateDecl *decl) const;

  /**
   * @brief Whether \p type is an integral type parameter (see
   * getIntegralTypeParams) of the function template whose generic function is
   * being serialized.
   */
  bool isIntegralTypeParam(clang::QualType type) const;

  /**
   * @brief Whether the function template whose generic function is being
   * serialized has integral type parameters (see getIntegralTypeParams).
   */
  bool hasIntegralTypeParams() const;

  /**
   * @brief Whether a call to the function template specialization \p decl
   * is verified against the generic function of its template, instead of
   * against a separately verified specialization.
   *
   * The generic function is verified with its type parameters treated as
   * values that are copied bitwise and destroyed without side effects. This
   * only holds for scalar type arguments. Its integral type parameters are
   * treated as integer types other than bool, so their type arguments must be
   * such builtin integer types.
   */
  bool usesGenericProof(const clang::FunctionDecl *decl) const;

  const clang::ASTContext &getASTContext() const { return *m_ASTContext; }

  const AnnotationManager &getAnnotationManager() const {
    return *m_annotationManager;
  }

  bool skipImplicitDecls() const { return m_skipImplicitDecls; }

  KJ_DISALLOW_COPY(ASTSerializer);

  ASTSerializer(const clang::ASTContext &ASTContext,
                const AnnotationManager &annotationManager,
                const GenericFallbacks &genericFallbacks,
                bool skipImplicitDecls)
      : m_ASTContext(&ASTContext), m_annotationManager(&annotationManager),
        m_genericFallbacks(&genericFallbacks),
        m_locationSerializer(ASTContext.getSourceManager(),
                             ASTContext.getLangOpts()),
        m_skipImplicitDecls(skipImplicitDecls) {}

  ASTSerializer(ASTSerializer &&) = default;
  ASTSerializer &operator=(ASTSerializer &&) = default;

private:
  const clang::ASTContext *m_ASTContext;
  const AnnotationManager *m_annotationManager;
  const GenericFallbacks *m_genericFallbacks;
  LocationSerializer m_locationSerializer;
  bool m_skipImplicitDecls;
  mutable llvm::DenseMap<int64_t, std::string> m_nameCache;
  mutable const clang::FunctionDecl *m_currentFunction = nullptr;
  mutable llvm::DenseMap<const clang::FunctionTemplateDecl *, bool>
      m_isVerifiedGenerically;
  mutable llvm::DenseMap<const clang::FunctionTemplateDecl *,
                         llvm::SmallBitVector>
      m_integralTypeParams;
};

} // namespace vf