#pragma once

#include "ASTSerializer.h"
#include "Annotation.h"
#include "Serializer.h"

namespace vf {

/**
 * @brief Specialized serializer for declarations.
 * 
 */
class DeclSerializer : public NodeSerializer<stubs::Decl, const clang::Decl *>,
                       public NodeSerializer<stubs::Decl, const Annotation &> {
public:
  void serialize(const clang::Decl *decl, LocBuilder locBuilder,
                 stubs::Decl::Builder declBuilder) const override;

  void serialize(const Annotation &annotation, LocBuilder locBuilder,
                 stubs::Decl::Builder declBuilder) const override;

  using NodeSerializer<stubs::Decl, const clang::Decl *>::serialize;
  using NodeSerializer<stubs::Decl, const Annotation &>::serialize;

  explicit DeclSerializer(const ASTSerializer &serializer)
      : m_ASTSerializer(&serializer) {}

private:
  const ASTSerializer *m_ASTSerializer;
};

} // namespace vf