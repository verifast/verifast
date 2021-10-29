#pragma once
#include "loc_serializer.h"
#include "Annotation.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/TypeLocVisitor.h"
#include "clang/AST/TypeVisitor.h"
#include "clang/Lex/Preprocessor.h"

namespace vf {

class AstSerializer;

/**
 * Serializer for the actual description of a node, i.e. its properties/fields.
 */
template <class StubsNode, class AstNode> class DescSerializer {
public:
  using DescBuilder = typename StubsNode::Builder;

  virtual ~DescSerializer() {}

protected:
  explicit DescSerializer(clang::ASTContext &context, AstSerializer *serializer,
                          DescBuilder builder)
      : _context(context), _serializer(serializer), _builder(builder) {}

  clang::ASTContext &_context;
  AstSerializer *_serializer;
  DescBuilder _builder;

  AstSerializer *getSerializer() { return _serializer; }

  virtual bool serializeDesc(const AstNode *node) = 0;

  const clang::ASTContext &getContext() const { return _context; }

  const clang::SourceManager &getSourceManager() const {
    return getContext().getSourceManager();
  }

  LLVM_ATTRIBUTE_NORETURN void unsupported(const AstNode *node,
                                           const clang::SourceRange range,
                                           const llvm::StringRef className) {
    llvm::report_fatal_error("Node of type '" + className + "' at '" +
                             range.printToString(getSourceManager()) +
                             "' is not supported.");
  }
};

/**
 * Serializer for nodes with an actual source range.
 * Serializes the source range of the node and its description.
 *
 * Be aware that skipping a node, by just returning true and not initializing a
 * description, will probably give unwanted results. This is due to the
 * side-effect that the description of a node is a union and it's default member
 * (the first one) would be selected. To make it easier to detect these
 * (unwanted) effects, every description's first union field has the name
 * 'UnionNotInitialized'.
 */
template <class StubsNode, class AstNode>
class NodeSerializer : public DescSerializer<StubsNode, AstNode> {
public:
  using NodeBuilder = typename stubs::Node<StubsNode>::Builder;

  explicit NodeSerializer(clang::ASTContext &context, AstSerializer *serializer,
                          stubs::Loc::Builder locBuilder,
                          typename StubsNode::Builder descBuilder)
      : DescSerializer<StubsNode, AstNode>(context, serializer, descBuilder),
        _locBuilder(locBuilder) {}

  explicit NodeSerializer(clang::ASTContext &context, AstSerializer *serializer,
                          NodeBuilder nodeBuilder)
      : NodeSerializer(context, serializer, nodeBuilder.initLoc(),
                       nodeBuilder.initDesc()) {}

  void serializeNode(const AstNode *node, const clang::SourceRange range,
                     const llvm::StringRef kind) {
    if (!this->serializeDesc(node))
      this->unsupported(node, range, kind);
    serializeSrcRange(_locBuilder, range, this->getSourceManager());
  }

protected:
  stubs::Loc::Builder _locBuilder;
};

struct StmtSerializer : public NodeSerializer<stubs::Stmt, clang::Stmt>,
                        public clang::ConstStmtVisitor<StmtSerializer, bool> {

  explicit StmtSerializer(clang::ASTContext &context, AstSerializer *serializer,
                          stubs::Loc::Builder &locBuilder,
                          stubs::Stmt::Builder &descBuilder)
      : NodeSerializer(context, serializer, locBuilder, descBuilder) {}

  explicit StmtSerializer(clang::ASTContext &context, AstSerializer *serializer,
                          NodeBuilder &nodeBuilder)
      : NodeSerializer(context, serializer, nodeBuilder) {}

  bool serializeDesc(const clang::Stmt *stmt) override {
    assert(stmt && "Statement should not be null");
    return Visit(stmt);
  }

  bool VisitCompoundStmt(const clang::CompoundStmt *stmt);

  bool VisitReturnStmt(const clang::ReturnStmt *stmt);

  bool VisitDeclStmt(const clang::DeclStmt *stmt);

  bool VisitExpr(const clang::Expr *expr);

  bool VisitIfStmt(const clang::IfStmt *stmt);

  bool VisitNullStmt(const clang::NullStmt *stmt);

  bool VisitWhileStmt(const clang::WhileStmt *stmt);

  bool VisitDoStmt(const clang::DoStmt *stmt);

  bool VisitBreakStmt(const clang::BreakStmt *stmt);

  bool VisitContinueStmt(const clang::ContinueStmt *stmt);

  bool VisitSwitchStmt(const clang::SwitchStmt *stmt);

  bool VisitCaseStmt(const clang::CaseStmt *stmt);

  bool VisitDefaultStmt(const clang::DefaultStmt *stmt);

private:
  template <class While>
  bool visitWhi(stubs::Stmt::While::Builder &builder, const While *stmt);
};

struct DeclSerializer : public NodeSerializer<stubs::Decl, clang::Decl>,
                        public clang::ConstDeclVisitor<DeclSerializer, bool> {

  explicit DeclSerializer(clang::ASTContext &context, AstSerializer *serializer,
                          stubs::Loc::Builder &locBuilder,
                          stubs::Decl::Builder &descBuilder)
      : NodeSerializer(context, serializer, locBuilder, descBuilder) {}

  explicit DeclSerializer(clang::ASTContext &context, AstSerializer *serializer,
                          NodeBuilder &nodeBuilder)
      : NodeSerializer(context, serializer, nodeBuilder) {}

  bool serializeDesc(const clang::Decl *decl) override {
    assert(decl && "Declaration should not be null");
    return Visit(decl);
  }

  bool VisitFunctionDecl(const clang::FunctionDecl *decl);

  bool VisitEmptyDecl(const clang::EmptyDecl *decl);

  bool VisitVarDecl(const clang::VarDecl *decl);

  bool VisitFieldDecl(const clang::FieldDecl *decl);

  bool VisitCXXRecordDecl(const clang::CXXRecordDecl *decl);

  // Note that this also handles conversion functions!
  bool VisitCXXMethodDecl(const clang::CXXMethodDecl *decl);

  bool VisitCXXConstructorDecl(const clang::CXXConstructorDecl *decl);

  bool VisitCXXDestructorDecl(const clang::CXXDestructorDecl *decl);

  bool VisitAccessSpecDecl(const clang::AccessSpecDecl *decl);

  bool VisitTypedefNameDecl(const clang::TypedefNameDecl *decl);

  bool VisitEnumDecl(const clang::EnumDecl *decl);

private:
  bool visitFunc(stubs::Decl::Function::Builder &builder,
                 const clang::FunctionDecl *decl);
};

struct ExprSerializer : public NodeSerializer<stubs::Expr, clang::Expr>,
                        public clang::ConstStmtVisitor<ExprSerializer, bool> {

  explicit ExprSerializer(clang::ASTContext &context, AstSerializer *serializer,
                          stubs::Loc::Builder &locBuilder,
                          stubs::Expr::Builder &descBuilder)
      : NodeSerializer(context, serializer, locBuilder, descBuilder) {}

  explicit ExprSerializer(clang::ASTContext &context, AstSerializer *serializer,
                          NodeBuilder &nodeBuilder)
      : NodeSerializer(context, serializer, nodeBuilder) {}

  bool serializeDesc(const clang::Expr *expr) override {
    assert(expr && "Expression should not be null");
    return Visit(expr);
  }

  bool VisitUnaryOperator(const clang::UnaryOperator *uo);

  bool VisitBinaryOperator(const clang::BinaryOperator *bo);

  bool VisitCXXBoolLiteralExpr(const clang::CXXBoolLiteralExpr *expr);

  bool VisitIntegerLiteral(const clang::IntegerLiteral *lit);

  bool VisitStringLiteral(const clang::StringLiteral *lit);

  bool VisitImplicitCastExpr(const clang::ImplicitCastExpr *expr);

  bool VisitCallExpr(const clang::CallExpr *expr);

  bool VisitDeclRefExpr(const clang::DeclRefExpr *expr);

  bool VisitMemberExpr(const clang::MemberExpr *expr);

  bool VisitCXXThisExpr(const clang::CXXThisExpr *expr);

  bool VisitCXXMemberCallExpr(const clang::CXXMemberCallExpr *expr);

  bool VisitCXXNewExpr(const clang::CXXNewExpr *expr);

  bool VisitCXXConstructExpr(const clang::CXXConstructExpr *expr);

  bool VisitConstantExpr(const clang::ConstantExpr *expr);

  bool VisitCXXNullPtrLiteralExpr(const clang::CXXNullPtrLiteralExpr *expr);

  bool VisitParenExpr(const clang::ParenExpr *expr);

  bool VisitCXXDeleteExpr(const clang::CXXDeleteExpr *expr);

private:
  bool serializeUnaryOperator(stubs::Expr::UnaryOp::Builder &builder,
                              const clang::UnaryOperator *uo);

  bool serializeBinaryOperator(stubs::Expr::BinaryOp::Builder &builder,
                               const clang::BinaryOperator *bo);

  bool visitCall(stubs::Expr::Call::Builder &builder,
                 const clang::CallExpr *expr);
};

struct TypeSerializer : private DescSerializer<stubs::Type, clang::Type>,
                        public clang::TypeVisitor<TypeSerializer, bool> {
  explicit TypeSerializer(clang::ASTContext &context, AstSerializer *serializer,
                          stubs::Type::Builder &builder)
      : DescSerializer(context, serializer, builder) {}

  using DescSerializer<stubs::Type, clang::Type>::DescBuilder;

  bool serializeDesc(const clang::Type *type) override {
    assert(type && "Type should not be null");
    return Visit(type);
  }

  void serialize(const clang::Type *type) {
    if (!this->serializeDesc(type))
      this->unsupported(type, {}, type->getTypeClassName());
  }

  bool VisitBuiltinType(const clang::BuiltinType *type);

  bool VisitPointerType(const clang::PointerType *type);

  bool VisitRecordType(const clang::RecordType *type);

  bool VisitEnumType(const clang::EnumType *type);

  bool VisitTypedefType(const clang::TypedefType *type);

  bool VisitElaboratedType(const clang::ElaboratedType *type);
};

struct TypeLocSerializer : private NodeSerializer<stubs::Type, clang::TypeLoc>,
                           clang::TypeLocVisitor<TypeLocSerializer, bool> {
  explicit TypeLocSerializer(clang::ASTContext &context,
                             AstSerializer *serializer,
                             stubs::Loc::Builder &locBuilder,
                             stubs::Type::Builder &descBuilder)
      : NodeSerializer(context, serializer, locBuilder, descBuilder) {}

  explicit TypeLocSerializer(clang::ASTContext &context,
                             AstSerializer *serializer,
                             NodeBuilder &nodeBuilder)
      : NodeSerializer(context, serializer, nodeBuilder) {}

  using NodeSerializer<stubs::Type, clang::TypeLoc>::NodeBuilder;

  bool serializeDesc(const clang::TypeLoc *type) override {
    assert(type && "TypeLoc should not be null");
    return Visit(*type);
  }

  void serializeNode(const clang::TypeLoc typeLoc) {
    auto range = typeLoc.getSourceRange();
    auto end = clang::Lexer::getLocForEndOfToken(
        range.getEnd(), 1, getSourceManager(), getContext().getLangOpts());
    clang::SourceRange spellingRange(range.getBegin(), end);
    serializeSrcRange(_locBuilder, spellingRange, this->getSourceManager());
    if (!this->serializeDesc(&typeLoc)) {
      // Try to delegate it to the type serializer
      TypeSerializer ser(_context, _serializer, _builder);
      auto type = typeLoc.getTypePtr();
      ser.serialize(type);
    }
  }

  bool VisitPointerTypeLoc(const clang::PointerTypeLoc type);
};

class AnnotationSerializer {
  clang::SourceManager &_SM;

public:
  explicit AnnotationSerializer(clang::SourceManager &SM) : _SM(SM) {}

  using ClauseBuilder = stubs::Clause::Builder;

  void serializeClause(ClauseBuilder &builder, const Annotation &ann) {
    auto locBuilder = builder.initLoc();
    serializeSrcRange(locBuilder, ann.getRange(), _SM);
    builder.setText(ann.getText().str());
  }

  template <class StubsNode>
  void serializeNode(stubs::Loc::Builder &locBuilder,
                     typename StubsNode::Builder &descBuilder,
                     const Annotation &ann) {
    serializeSrcRange(locBuilder, ann.getRange(), _SM);
    descBuilder.setAnn(ann.getText().str());
  }
};

} // namespace vf