#pragma once

#include "ASTSerializer.h"
#include "Serializer.h"

namespace vf {

/**
 * @brief Serializer for types that are not associated with a source range.
 *
 */
class TypeSerializer
    : public Serializer<const clang::Type *, stubs::Type::Builder> {
public:
  void serialize(const clang::Type *type,
                 stubs::Type::Builder builder) const override;

  explicit TypeSerializer(const ASTSerializer &serializer)
      : m_ASTSerializer(&serializer) {}

private:
  const ASTSerializer *m_ASTSerializer;
};

/**
 * @brief Serializer for types that have a source range.
 *
 */
class TypeLocSerializer : public NodeSerializer<stubs::Type, clang::TypeLoc> {
public:
  void serialize(clang::TypeLoc typeLoc, LocBuilder locBuilder,
                 stubs::Type::Builder typeBuilder) const override;

  using NodeSerializer::serialize;

  explicit TypeLocSerializer(const ASTSerializer &serializer)
      : m_ASTSerializer(&serializer) {}

private:
  const ASTSerializer *m_ASTSerializer;
};

} // namespace vf