#pragma once

#include "stubs_ast.capnp.h"

namespace vf {

using LocBuilder = stubs::Loc::Builder;

template <typename T> using NodeBuilder = typename stubs::Node<T>::Builder;

using DeclNodeBuilder = NodeBuilder<stubs::Decl>;
using StmtNodeBuilder = NodeBuilder<stubs::Stmt>;
using ExprNodeBuilder = NodeBuilder<stubs::Expr>;
using TypeNodeBuilder = NodeBuilder<stubs::Type>;

template <typename T>
using ListBuilder = typename capnp::List<T, capnp::Kind::STRUCT>::Builder;

/**
 * @brief Interface for serializers.
 *
 * @tparam Serializable Type that can be serialized with this serializer
 * @tparam SerializeArgs Extra argument types passed to `serialize`
 */
template <typename Serializable, typename... SerializeArgs> class Serializer {
public:
  virtual void serialize(Serializable serializable,
                         SerializeArgs... args) const = 0;
  virtual ~Serializer() = default;
};

/**
 * @brief Interface for serializers that serialize to a node which
 * consists of a location and a description.
 *
 * @tparam Stub Type of the target node's description
 * @tparam Serializable Type of item that can be serialized to a node
 */
template <typename Stub, typename Serializable>
class NodeSerializer
    : public Serializer<Serializable, NodeBuilder<Stub>>,
      public Serializer<Serializable, LocBuilder, typename Stub::Builder> {
public:
  /**
   * @brief Serialize a `serializable` to the builder of a target node.
   *
   * @param serializable Item to serialize
   * @param builder Builder of the target node
   */
  void serialize(Serializable serializable,
                 NodeBuilder<Stub> builder) const override {
    LocBuilder locBuilder = builder.initLoc();
    typename Stub::Builder descBuilder = builder.initDesc();
    serialize(serializable, locBuilder, descBuilder);
  }

  /**
   * @brief Serialize a `serializable` in a decomposed way to the `locBuilder`
   * and `descBuilder` of the target node.
   *
   * @param serializable Item to serialize
   * @param locBuilder Builder of the target node
   * @param descBuilder Description builder of the target node
   */
  void serialize(Serializable serializable, LocBuilder locBuilder,
                 typename Stub::Builder descBuilder) const override = 0;
};

} // namespace vf