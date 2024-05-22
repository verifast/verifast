#pragma once

#include "ASTSerializer.h"
#include "Annotation.h"
#include "Serializer.h"
#include "stubs_ast.capnp.h"
#include "clang/AST/Stmt.h"

namespace vf {

/**
 * @brief Specialized serializer for statements.
 * 
 */
class StmtSerializer : public NodeSerializer<stubs::Stmt, const clang::Stmt *>,
                       public NodeSerializer<stubs::Stmt, const Annotation &> {
public:
  void serialize(const clang::Stmt *stmt, stubs::Loc::Builder locBuilder,
                 stubs::Stmt::Builder stmtBuilder) const override;

  void serialize(const Annotation &annotation, stubs::Loc::Builder locBuilder,
                 stubs::Stmt::Builder stmtBuilder) const override;

  using NodeSerializer<stubs::Stmt, const clang::Stmt *>::serialize;
  using NodeSerializer<stubs::Stmt, const Annotation &>::serialize;

  explicit StmtSerializer(const ASTSerializer &serializer)
      : m_ASTSerializer(&serializer) {}

private:
  const ASTSerializer *m_ASTSerializer;
};

} // namespace vf