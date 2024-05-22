#pragma once

#include "ASTSerializer.h"
#include "Serializer.h"
#include "stubs_ast.capnp.h"
#include "clang/AST/Expr.h"

namespace vf {

class ExprSerializer : public NodeSerializer<stubs::Expr, const clang::Expr *> {
public:
  void serialize(const clang::Expr *expr, stubs::Loc::Builder locBuilder,
                 stubs::Expr::Builder exprBuilder) const override;

  using NodeSerializer::serialize;

  explicit ExprSerializer(const ASTSerializer &serializer)
      : m_ASTSerializer(&serializer) {}

private:
  const ASTSerializer *m_ASTSerializer;
};

} // namespace vf