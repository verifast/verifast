#pragma once
#include "AnnotationStore.h"
#include "FunctionMangler.h"
#include "InclusionContext.h"
#include "NodeSerializer.h"
#include "capnp/orphan.h"
#include "llvm/ADT/SmallVector.h"
#include <kj/common.h>
#include <unordered_map>

namespace vf {

/**
 * Wrapper for data related to orphans. Useful when first serializing to
 * orphans instead of serializing to an actual message. Holds two orphans: one
 * for the location of the node and another for the properties of the node.
 */
template <class StubsNode> struct NodeOrphan {
  using loc_orphan = capnp::Orphan<stubs::Loc>;
  using node_orphan = capnp::Orphan<StubsNode>;
  loc_orphan locOrphan;
  node_orphan nodeOrphan;

  explicit NodeOrphan(loc_orphan &&lOrphan, node_orphan &&dOrphan)
      : locOrphan(std::move(lOrphan)), nodeOrphan(std::move(dOrphan)) {}
};

using DeclNodeOrphan = NodeOrphan<stubs::Decl>;

/**
 * Wrapper for all serializers: serializes declarations, statements,
 * expressions, types and annotations. It simply delegates serialization to the
 * corresponding serializer.
 */
class AstSerializer {
  clang::ASTContext &m_ASTContext;
  clang::SourceManager &m_SM;
  InclusionContext &m_inclContext;

  FunctionMangler m_funcMangler;

  AnnotationSerializer m_textSerializer;
  AnnotationStore &m_store;
  std::unordered_map<unsigned, llvm::SmallVector<DeclNodeOrphan, 8>>
      m_fileDeclsMap;
  std::unordered_map<unsigned, clang::SourceLocation> m_firstDeclLocMap;

  bool m_serializeImplicitDecls;

  /**
   * Serialize a declaration to this instance's declaration map of orphans.
   * First checks for annotation declarations an d serializes them to the map
   * prior to serializing the declaration itself.
   * @param decl Declaration to serialize.
   * @param orphanage Orphanage to be able to create new orphans.
   */
  void serializeDeclToDeclMap(const clang::Decl *decl,
                              capnp::Orphanage &orphanage);

  void updateFirstDeclLoc(unsigned fd, const clang::SourceLocation loc);

  llvm::Optional<clang::SourceLocation> getFirstDeclLocOpt(unsigned fd) const;

public:
  explicit AstSerializer(clang::ASTContext &context, AnnotationStore &store,
                         InclusionContext &inclContext,
                         bool serializeImplicitDecls)
      : m_ASTContext(context), m_SM(context.getSourceManager()),
        m_inclContext(inclContext), m_textSerializer(context.getSourceManager()),
        m_funcMangler(context), m_store(store),
        m_serializeImplicitDecls(serializeImplicitDecls) {}

  KJ_DISALLOW_COPY(AstSerializer);

  AnnotationStore &getAnnStore() { return m_store; }

  /**
   * Serializes a declaration.
   * @param builder builder that is used to serialize the declaration.
   * @param decl declaration that has to be serialized.
   */
  void serializeDecl(DeclSerializer::NodeBuilder &builder,
                     const clang::Decl *decl);

  /**
   * Serializes a statement.
   * @param builder builder that is used to serialize the statement.
   * @param stmt statement that has to be serialized.
   */
  void serializeStmt(StmtSerializer::NodeBuilder &builder,
                     const clang::Stmt *stmt);

  /**
   * Serializes an expression.
   * @param builder builder that is used to serialize the expression.
   * @param expr expression that has to be serialized.
   */
  void serializeExpr(ExprSerializer::NodeBuilder &builder,
                     const clang::Expr *expr);

  /**
   * Serializes a type with a location.
   * @param builder builder that is used to serialize the type.
   * @param typeLoc wrapper that contains the type and source information for
   * that type.
   */
  void serializeTypeLoc(TypeLocSerializer::NodeBuilder &builder,
                        const clang::TypeLoc typeLoc);

  /**
   * Serializes a type.
   * @param builder builder that is used to serialize the type.
   * @param type type to serialize.
   * that type.
   */
  void serializeQualType(TypeSerializer::DescBuilder &builder,
                         const clang::QualType type);

  void serializeParams(
      capnp::List<stubs::Param, capnp::Kind::STRUCT>::Builder &builder,
      llvm::ArrayRef<clang::ParmVarDecl *> params);

  /**
   * Serializes a declaration. Useful when serializing to orphans instead of
   * serializing to an actual message.
   * @param locBuilder builder that is used to serialize the location of the
   * declaration.
   * @param builder builder that is used to serialize the properties of the
   * declaration.
   * @param decl declaration that has to be serialized.
   */
  void serializeNodeDecomposed(stubs::Loc::Builder &locBuilder,
                               stubs::Decl::Builder &builder,
                               const clang::Decl *decl);

  /**
   * Serializes a statement. Useful when serializing to orphans instead of
   * serializing to an actual message.
   * @param locBuilder builder that is used to serialize the location of the
   * statement.
   * @param builder builder that is used to serialize the properties of the
   * statement.
   * @param stmt statement that has to be serialized.
   */
  void serializeNodeDecomposed(stubs::Loc::Builder &locBuilder,
                               stubs::Stmt::Builder &builder,
                               const clang::Stmt *stmt);

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
  void serializeTU(stubs::TU::Builder &builder,
                   const clang::TranslationUnitDecl *tu);

  /**
   * Serializes an annotation. E.g. in a loop contract or function contract.
   * Cannot be used for annotations that derive from other nodes (like a
   * declaration annotation).
   *
   * @param builder builder that is used to serialize the annotation.
   * @param ann annotation to serialize.
   */
  void serializeAnnotationClause(AnnotationSerializer::ClauseBuilder &builder,
                                 const Annotation &ann) {
    m_textSerializer.serializeClause(builder, ann);
  }

  void serializeAnnotationClauses(
      capnp::List<stubs::Clause, capnp::Kind::STRUCT>::Builder &builder,
      const clang::ArrayRef<Annotation> anns);

  /**
   * Serializes an annotation that derives from another node (like a declaration
   * annotation or statement annotation).
   *
   * @tparam StubsNode the type of base node for serialization. E.g. a
   * declaration or statement.
   * @param locBuilder builder that is used to serialize the location of the
   * statement.
   * @param builder builder that is used to serialize the actual annotation
   * text.
   * @param ann annotation to serialize.
   */
  template <class StubsNode>
  void serializeAnnotationDecomposed(stubs::Loc::Builder &locBuilder,
                                     typename StubsNode::Builder &descBuilder,
                                     const Annotation &ann) {
    m_textSerializer.serializeNode<StubsNode>(locBuilder, descBuilder, ann);
  }

  /**
   * Serializes to an orphan. An orphan is not part (yet) of an actual
   * serialized message. It can later be adopted to a message. This is useful
   * when the the number of nodes is not known yet. These nodes can be
   * serialized to a list of orphans and later be adopted to an actual message.
   * Serializing to an orphans does not consume memory in a message.
   *
   * @tparam ToSerialize type of what has to be serialized.
   * @tparam StubsNode corresponding type in the serialization.
   * @param ser what has to be serialized.
   * @param orphanage factory to create orphans that can be serialied to.
   * @param[in, out] orphans collection of serialized orphans. A new orphan
   * containing the serialized object will be added to the back of the
   * collection.
   */
  template <class ToSerialize, class StubsNode>
  void
  serializeToOrphan(const ToSerialize *ser, capnp::Orphanage &orphanage,
                    llvm::SmallVectorImpl<NodeOrphan<StubsNode>> &orphans) {
    orphans.emplace_back(orphanage.newOrphan<stubs::Loc>(),
                         orphanage.newOrphan<StubsNode>());
    auto &no = orphans.back();
    auto locBuilder = no.locOrphan.get();
    auto descBuilder = no.nodeOrphan.get();
    serializeNodeDecomposed(locBuilder, descBuilder, ser);
  }

  /**
   * Serializes an annotation to an orphan.
   *
   * @tparam StubsNode the type of base node for serialization. E.g. a
   * declaration or statement.
   * @param ann annotation to serialize.
   * @param orphanage factory to create orphans that can be serialied to.
   * @param[in, out] orphans collection of serialized orphans. A new orphan
   * containing the serialized annotation will be added to the back of the
   * collection.
   */
  template <class StubsNode>
  void
  serializeAnnToOrphan(const Annotation &ann, capnp::Orphanage &orphanage,
                       llvm::SmallVectorImpl<NodeOrphan<StubsNode>> &orphans) {
    orphans.emplace_back(orphanage.newOrphan<stubs::Loc>(),
                         orphanage.newOrphan<StubsNode>());
    auto &dno = orphans.back();
    auto locBuilder = dno.locOrphan.get();
    auto descBuilder = dno.nodeOrphan.get();
    serializeAnnotationDecomposed<StubsNode>(locBuilder, descBuilder, ann);
  }

  /**
   * Serializes multiple annotations to orphans.
   * @tparam StubsNode the type of base node for serialization. E.g. a
   * declaration or statement.
   * @tparam Container type of the container that holds the annotations to
   * serialize.
   * @param annotations container that holds the the annotations to serialize to
   * orphans.
   * @param orphanage factory to create orphans that can be serialied to.
   * @param orphans collection of serialized orphans. New orphans
   * containing the serialized annotations will be added to the back of the
   * collection.
   */
  template <class StubsNode>
  void serializeAnnsToOrphans(
      const llvm::ArrayRef<Annotation> &annotations,
      capnp::Orphanage &orphanage,
      llvm::SmallVectorImpl<NodeOrphan<StubsNode>> &orphans) {
    for (auto &ann : annotations) {
      serializeAnnToOrphan(ann, orphanage, orphans);
    }
  }

  /**
   * Adopt a vector of orphans to a list builder. This adopts the serialized
   * orphan objects to an actual message.
   * @tparam StubsNode type of serialized node in the vector of orphans.
   * @param orphans vector of orphans that has to be adopted.
   * @param listBuilder builder of a list that will adopt the given orphans.
   */
  template <class StubsNode>
  static void adoptOrphansToListBuilder(
      llvm::SmallVectorImpl<NodeOrphan<StubsNode>> &orphans,
      typename capnp::List<stubs::Node<StubsNode>, capnp::Kind::STRUCT>::Builder
          listBuilder) {
    size_t i(0);
    for (auto &no : orphans) {
      auto builder = listBuilder[i++];
      builder.adoptLoc(std::move(no.locOrphan));
      builder.adoptDesc(std::move(no.nodeOrphan));
    }
  }

  void validateIncludesBeforeFirstDecl(
      unsigned fd,
      clang::ArrayRef<std::reference_wrapper<const IncludeDirective>>
          orderedDirectives) const;

  llvm::StringRef getMangledName(const clang::CXXConstructorDecl *decl) {
    return m_funcMangler.mangleCtor(decl);
  }

  llvm::StringRef getMangledName(const clang::CXXDestructorDecl *decl) {
    return m_funcMangler.mangleDtor(decl);
  }

  llvm::StringRef getMangledName(const clang::FunctionDecl *decl) {
    return m_funcMangler.mangleFunc(decl);
  }
};

} // namespace vf