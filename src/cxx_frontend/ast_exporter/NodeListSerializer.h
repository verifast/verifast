#pragma once

#include "DeclSerializer.h"
#include "StmtSerializer.h"
#include "capnp/orphan.h"
#include "stubs_ast.capnp.h"
#include "clang/AST/ASTContext.h"
#include "llvm/ADT/SmallVector.h"

namespace vf {

/**
 * @brief Serializer for a list of nodes. Internally uses orphans for
 * serialization. The serializer must be adopted to a concrete list-builder of
 * `Stubs` in order to adopt the internal list of orphans to the message.
 *
 * This class cannot be copied since orphans can only be moved.
 *
 * @tparam Stub Type of the target node's description
 * @tparam NodeSerializerImpl Type of concrete `NodeSerializer` that can
 * serialize nodes.
 */
template <typename Stub, typename NodeSerializerImpl> class NodeListSerializer {
public:
  using Node = stubs::Node<Stub>;
  using ListBuilder = typename capnp::List<Node, capnp::Kind::STRUCT>::Builder;

  /// @returns The number of serialized items.
  size_t size() const { return m_orphans.size(); }

  template <typename T> void serialize(T item) {
    NodeOrphan &nodeOrphan = m_orphans.emplace_back(
        m_orphanage.newOrphan<stubs::Loc>(), m_orphanage.newOrphan<Stub>());
    m_serializer.serialize(item, nodeOrphan.locOrphan.get(),
                           nodeOrphan.descOrphan.get());
  }

  template <typename T> void serialize(llvm::ArrayRef<T> container) {
    for (const T &item : container) {
      serialize(item);
    }
  }

  template <typename T> NodeListSerializer &operator<<(T item) {
    serialize(item);
    return *this;
  }

  template <typename T>
  NodeListSerializer &operator<<(llvm::ArrayRef<T> container) {
    serialize(container);
    return *this;
  }

  /**
   * @brief Adopt the internal list of orphans to a concrete list-builder.
   * Orphans can only be adopted once.
   *
   * @param builder Concrete list-builder with a fixed size that must be equal
   * to this serializer's size.
   */
  void adoptToListBuilder(ListBuilder builder) {
    assert(size() == builder.size() && "Target builder has wrong size");

    size_t i(0);
    for (auto &nodeOrphan : m_orphans) {
      auto itemBuilder = builder[i++];
      itemBuilder.adoptLoc(std::move(nodeOrphan.locOrphan));
      itemBuilder.adoptDesc(std::move(nodeOrphan.descOrphan));
    }

    m_orphans.clear();
  }

  KJ_DISALLOW_COPY(NodeListSerializer);

  NodeListSerializer(capnp::Orphanage orphanage, NodeSerializerImpl serializer)
      : m_orphanage(orphanage), m_serializer(serializer) {}

  NodeListSerializer(NodeListSerializer &&) = default;
  NodeListSerializer &operator=(NodeListSerializer &&) = default;

private:
  struct NodeOrphan {
    using LocOrphan = capnp::Orphan<stubs::Loc>;
    using DescOrphan = capnp::Orphan<Stub>;

    KJ_DISALLOW_COPY(NodeOrphan);

    explicit NodeOrphan(LocOrphan locOrphan, DescOrphan descOrphan)
        : locOrphan(std::move(locOrphan)), descOrphan(std::move(descOrphan)) {}

    NodeOrphan(NodeOrphan &&) = default;
    NodeOrphan &operator=(NodeOrphan &&) = default;

    LocOrphan locOrphan;
    DescOrphan descOrphan;
  };

  capnp::Orphanage m_orphanage;
  NodeSerializerImpl m_serializer;
  llvm::SmallVector<NodeOrphan> m_orphans;
};

using DeclListSerializer = NodeListSerializer<stubs::Decl, DeclSerializer>;
using StmtListSerializer = NodeListSerializer<stubs::Stmt, StmtSerializer>;

} // namespace vf