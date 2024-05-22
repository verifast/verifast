#pragma once

#include "AnnotationManager.h"
#include "LocationSerializer.h"
#include "stubs_ast.capnp.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"
#include "clang/AST/TypeLoc.h"
#include "llvm/ADT/DenseMap.h"

namespace vf {

/**
 * @brief Serializer for various nodes in the AST of a translation unit.
 *
 */
class ASTSerializer {
public:
  void serialize(DeclNodeBuilder builder, const clang::Decl *decl) const;

  void serialize(StmtNodeBuilder builder, const clang::Stmt *stmt) const;

  void serialize(ExprNodeBuilder builder, const clang::Expr *expr) const;

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

  const clang::ASTContext &getASTContext() const { return *m_ASTContext; }

  const AnnotationManager &getAnnotationManager() const {
    return *m_annotationManager;
  }

  bool skipImplicitDecls() const { return m_skipImplicitDecls; }

  KJ_DISALLOW_COPY(ASTSerializer);

  ASTSerializer(const clang::ASTContext &ASTContext,
                const AnnotationManager &annotationManager,
                bool skipImplicitDecls)
      : m_ASTContext(&ASTContext), m_annotationManager(&annotationManager),
        m_locationSerializer(ASTContext.getSourceManager(),
                             ASTContext.getLangOpts()),
        m_skipImplicitDecls(skipImplicitDecls) {}

  ASTSerializer(ASTSerializer &&) = default;
  ASTSerializer &operator=(ASTSerializer &&) = default;

private:
  const clang::ASTContext *m_ASTContext;
  const AnnotationManager *m_annotationManager;
  LocationSerializer m_locationSerializer;
  bool m_skipImplicitDecls;
  mutable llvm::DenseMap<int64_t, std::string> m_nameCache;
};

} // namespace vf