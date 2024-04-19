#pragma once
#include "Annotation.h"
#include "Concept.h"
#include "Inclusion.h"
#include "NodeSerializer.h"
#include "capnp/orphan.h"
#include "llvm/ADT/SmallVector.h"
#include <kj/common.h>
#include <string.h>
#include <unordered_map>

namespace vf {

template <IsStubsNode StubsNode, IsAstNode AstNode, typename Serializer>
class NodeListSerializer;

using DeclListSerializer =
    NodeListSerializer<stubs::Decl, clang::Decl, DeclSerializer>;
using StmtListSerializer =
    NodeListSerializer<stubs::Stmt, clang::Stmt, StmtSerializer>;

/**
 * Wrapper for all serializers: serializes declarations, statements,
 * expressions, types and annotations. It simply delegates serialization to the
 * corresponding serializer.
 */
class AstSerializer {
  clang::ASTContext &m_ASTContext;
  clang::SourceManager &m_SM;
  InclusionContext &m_inclContext;

  capnp::Orphanage m_orphanage;

  TextSerializer m_textSerializer;
  AnnotationStore &m_store;
  std::unordered_map<unsigned, std::unique_ptr<DeclListSerializer>>
      m_fileDeclsMap;
  std::unordered_map<unsigned, clang::SourceLocation> m_firstDeclLocMap;

  bool m_serializeImplicitDecls;

  /**
   * Serialize a declaration to this instance's declaration map of orphans.
   * First checks for annotation declarations and serializes them to the map
   * prior to serializing the declaration itself.
   * @param decl Declaration to serialize.
   * @param orphanage Orphanage to be able to create new orphans.
   */
  void serializeDeclToDeclMap(const clang::Decl *decl,
                              capnp::Orphanage &orphanage);

  void updateFirstDeclLoc(unsigned fd, const clang::SourceLocation loc);

  llvm::Optional<clang::SourceLocation> getFirstDeclLocOpt(unsigned fd) const;

  void printQualifiedName(const clang::NamedDecl *decl,
                          llvm::raw_string_ostream &os) const;

  DeclListSerializer &getDeclListSerializer(unsigned fd);

public:
  explicit AstSerializer(clang::ASTContext &context, AnnotationStore &store,
                         InclusionContext &inclContext,
                         capnp::Orphanage orphanage,
                         bool serializeImplicitDecls)
      : m_ASTContext(context), m_SM(context.getSourceManager()),
        m_inclContext(inclContext), m_orphanage(orphanage),
        m_textSerializer(context), m_store(store),
        m_serializeImplicitDecls(serializeImplicitDecls) {}

  KJ_DISALLOW_COPY(AstSerializer);

  clang::DiagnosticsEngine &getDiagsEngine() const {
    return m_ASTContext.getDiagnostics();
  }

  AnnotationStore &getAnnStore() { return m_store; }

  const clang::ASTContext &getASTContext() const { return m_ASTContext; }

  bool serializeImplicitDecls() const { return m_serializeImplicitDecls; }

  /**
   * Serializes a declaration.
   * @param builder builder that is used to serialize the declaration.
   * @param decl declaration that has to be serialized.
   */
  void serializeDecl(DeclSerializer::NodeBuilder builder,
                     const clang::Decl *decl);

  /**
   * Serializes a statement.
   * @param builder builder that is used to serialize the statement.
   * @param stmt statement that has to be serialized.
   */
  void serializeStmt(StmtSerializer::NodeBuilder builder,
                     const clang::Stmt *stmt);

  /**
   * Serializes an expression.
   * @param builder builder that is used to serialize the expression.
   * @param expr expression that has to be serialized.
   */
  void serializeExpr(ExprSerializer::NodeBuilder builder,
                     const clang::Expr *expr);

  /**
   * Serializes a type with a location.
   * @param builder builder that is used to serialize the type.
   * @param typeLoc wrapper that contains the type and source information for
   * that type.
   */
  void serializeTypeLoc(TypeLocSerializer::NodeBuilder builder,
                        const clang::TypeLoc typeLoc);

  /**
   * Serializes a type.
   * @param builder builder that is used to serialize the type.
   * @param type type to serialize.
   * that type.
   */
  void serializeQualType(TypeSerializer::DescBuilder builder,
                         const clang::QualType type);

  void serializeParams(
      capnp::List<stubs::Param, capnp::Kind::STRUCT>::Builder builder,
      llvm::ArrayRef<clang::ParmVarDecl *> params);

  /**
   * Serializes a translation unit. A serialized translation unit consists of a
   * list of declarations and a list consisting of file entries. Those entries
   * are simple `<unsigned, string>` pairs. I.e. a mapping from identifiers to
   * file names. This information can later be used during deserialization as
   * serialized source locations contain identifiers instead of complete file
   * names to reduce redundancy.
   *
   * @param builder builder that is used to serialize the translation unit.
   * @param tu translation unit to serialize.
   */
  void serializeTU(stubs::TU::Builder builder,
                   const clang::TranslationUnitDecl *tu);

  /**
   * Serializes an annotation. E.g. in a loop contract or function contract.
   * Cannot be used for annotations that derive from other nodes (like a
   * declaration annotation).
   *
   * @param builder builder that is used to serialize the annotation.
   * @param ann annotation to serialize.
   */
  void serializeAnnotationClause(TextSerializer::ClauseBuilder builder,
                                 const Annotation &ann) {
    m_textSerializer.serializeClause(builder, ann);
  }

  void serializeAnnotationClauses(
      capnp::List<stubs::Clause, capnp::Kind::STRUCT>::Builder builder,
      const clang::ArrayRef<Annotation> anns);

  void validateIncludesBeforeFirstDecl(
      unsigned fd,
      clang::ArrayRef<std::reference_wrapper<const IncludeDirective>>
          orderedDirectives) const;

  std::string getQualifiedName(const clang::NamedDecl *decl) const;

  std::string getQualifiedFuncName(const clang::FunctionDecl *decl) const;
};

template <IsStubsNode StubsNode, IsAstNode AstNode, typename Serializer>
class NodeListSerializer {
  static_assert(
      std::is_base_of_v<NodeSerializer<StubsNode, AstNode>, Serializer>,
      "Serializer must be an appropriate instance of NodeSerializer");

public:
  using ListBuilder = typename capnp::List<stubs::Node<StubsNode>,
                                           capnp::Kind::STRUCT>::Builder;
  using LocBuilder = stubs::Loc::Builder;
  using DescBuilder = typename StubsNode::Builder;

  KJ_DISALLOW_COPY(NodeListSerializer);

  NodeListSerializer(capnp::Orphanage orphanage, AstSerializer &serializer)
      : m_orphanage(orphanage), m_serializer(serializer) {}

  NodeListSerializer(NodeListSerializer &&) = default;
  NodeListSerializer &operator=(NodeListSerializer &&) = default;

  template <typename T> void serialize(const T *item) {
    m_orphans.emplace_back(m_orphanage.newOrphan<stubs::Loc>(),
                           m_orphanage.newOrphan<StubsNode>());
    auto &nodeOrphan = m_orphans.back();
    serialize(nodeOrphan.locOrphan.get(), nodeOrphan.descOrphan.get(), item);
  }

  template <typename Container, typename RetType>
  using enable_if_iterable = typename std::enable_if<
      std::is_same_v<decltype(std::begin(std::declval<Container>())),
                     decltype(std::end(std::declval<Container>()))>,
      RetType>::type;

  template <typename Container>
  enable_if_iterable<Container, void> serialize(const Container &container) {
    for (auto it = container.begin(); it != container.end(); ++it) {
      serialize(it);
    }
  }

  size_t size() const { return m_orphans.size(); }

  template <typename T> NodeListSerializer &operator<<(const T *item) {
    serialize(item);
    return *this;
  }

  template <typename Container>
  enable_if_iterable<Container, NodeListSerializer &>
  operator<<(const Container &container) {
    serialize(container);
    return *this;
  }

  void adoptListToBuilder(ListBuilder builder) {
    assert(size() >= builder.size() && "Target builder too small");

    size_t i(0);
    for (auto &nodeOrphan : m_orphans) {
      auto elementBuilder = builder[i++];
      elementBuilder.adoptLoc(std::move(nodeOrphan.locOrphan));
      elementBuilder.adoptDesc(std::move(nodeOrphan.descOrphan));
    }
  }

private:
  struct NodeOrphan {
    using LocOrphan = capnp::Orphan<stubs::Loc>;
    using DescOrphan = capnp::Orphan<StubsNode>;

    KJ_DISALLOW_COPY(NodeOrphan);

    explicit NodeOrphan(LocOrphan locOrphan, DescOrphan descOrphan)
        : locOrphan(std::move(locOrphan)), descOrphan(std::move(descOrphan)) {}

    NodeOrphan(NodeOrphan &&) = default;
    NodeOrphan &operator=(NodeOrphan &&) = default;

    LocOrphan locOrphan;
    DescOrphan descOrphan;
  };

  void serialize(LocBuilder locBuilder, DescBuilder descBuilder,
                 const AstNode *node) {
    Serializer ser(m_serializer.getASTContext(), m_serializer, locBuilder,
                   descBuilder);
    ser.serialize(node);
  }

  void serialize(LocBuilder locBuilder, DescBuilder descBuilder,
                 const Text *text) {
    TextSerializer ser(m_serializer.getASTContext());
    ser.serializeNode<StubsNode>(locBuilder, descBuilder, text);
  }

  AstSerializer &m_serializer;
  capnp::Orphanage m_orphanage;
  llvm::SmallVector<NodeOrphan> m_orphans;
};

} // namespace vf