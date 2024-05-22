#include "ASTSerializer.h"
#include "DeclSerializer.h"
#include "ExprSerializer.h"
#include "LocationSerializer.h"
#include "StmtSerializer.h"
#include "TypeSerializer.h"

namespace {
void printQualifiedName(const clang::NamedDecl *decl,
                        llvm::raw_string_ostream &os,
                        const clang::PrintingPolicy &policy) {
  decl->printQualifiedName(os, policy);
}
} // namespace

namespace vf {

void ASTSerializer::serialize(DeclNodeBuilder builder,
                              const clang::Decl *decl) const {
  DeclSerializer serializer(*this);
  serializer.serialize(decl, builder);
}

void ASTSerializer::serialize(StmtNodeBuilder builder,
                              const clang::Stmt *stmt) const {
  StmtSerializer serializer(*this);
  serializer.serialize(stmt, builder);
}

void ASTSerializer::serialize(ExprNodeBuilder builder,
                              const clang::Expr *expr) const {
  ExprSerializer serializer(*this);
  serializer.serialize(expr, builder);
}

void ASTSerializer::serialize(TypeNodeBuilder builder,
                              clang::TypeLoc typeLoc) const {
  TypeLocSerializer serializer(*this);
  serializer.serialize(typeLoc, builder);
}

void ASTSerializer::serialize(stubs::Type::Builder builder,
                              clang::QualType type) const {
  TypeSerializer serializer(*this);
  serializer.serialize(type.getTypePtr(), builder);
}

void ASTSerializer::serialize(LocBuilder locBuilder,
                              clang::SourceRange range) const {
  m_locationSerializer.serialize(range, locBuilder);
}

void ASTSerializer::serialize(
    ListBuilder<stubs::Param> builder,
    llvm::ArrayRef<clang::ParmVarDecl *> params) const {
  assert(builder.size() == params.size() && "Target builder has wrong size");

  size_t i(0);
  for (const clang::ParmVarDecl *param : params) {
    stubs::Param::Builder paramBuilder = builder[i++];
    TypeNodeBuilder typeBuilder = paramBuilder.initType();

    paramBuilder.setName(param->getDeclName().getAsString());

    if (param->hasDefaultArg()) {
      ExprNodeBuilder exprBuilder = paramBuilder.initDefault();
      serialize(exprBuilder, param->getDefaultArg());
    }

    clang::TypeSourceInfo *typeSourceInfo = param->getTypeSourceInfo();
    if (typeSourceInfo) {
      serialize(typeBuilder, typeSourceInfo->getTypeLoc());
      continue;
    }

    serialize(typeBuilder.initDesc(), param->getType());
  }
}

void ASTSerializer::serialize(stubs::Clause::Builder builder,
                              const Text &text) const {
  serialize(builder.initLoc(), text.getRange());
  builder.setText(text.getText().data());
}

namespace {

template <typename T>
void serializeTextArray(ListBuilder<stubs::Clause> builder,
                        llvm::ArrayRef<T> textArray,
                        const ASTSerializer *serializer) {
  assert(builder.size() == textArray.size() && "Target builder has wrong size");

  size_t i(0);
  for (const T &text : textArray) {
    stubs::Clause::Builder annotationBuilder = builder[i++];
    serializer->serialize(annotationBuilder, text);
  }
}

} // namespace

void ASTSerializer::serialize(ListBuilder<stubs::Clause> builder,
                              llvm::ArrayRef<Text> textArray) const {
  serializeTextArray(builder, textArray, this);
}

void ASTSerializer::serialize(ListBuilder<stubs::Clause> builder,
                              llvm::ArrayRef<Annotation> annotations) const {
  serializeTextArray(builder, annotations, this);
}

std::string
ASTSerializer::getQualifiedName(const clang::NamedDecl *decl) const {
  auto it = m_nameCache.find(decl->getID());

  if (it != m_nameCache.end()) {
    return it->getSecond();
  }

  std::string s;
  llvm::raw_string_ostream os(s);
  printQualifiedName(decl, os, m_ASTContext->getPrintingPolicy());
  os.flush();

  m_nameCache.insert({decl->getID(), s});

  return s;
}

std::string
ASTSerializer::getQualifiedFuncName(const clang::FunctionDecl *decl) const {
  auto it = m_nameCache.find(decl->getID());

  if (it != m_nameCache.end()) {
    return it->getSecond();
  }

  std::string s;
  llvm::raw_string_ostream os(s);
  printQualifiedName(decl, os, m_ASTContext->getPrintingPolicy());
  os << "(";
  auto *param = decl->param_begin();
  while (param != decl->param_end()) {
    (*param)->getOriginalType().print(os, m_ASTContext->getPrintingPolicy());
    ++param;
    if (param != decl->param_end()) {
      os << ", ";
    }
  }
  os << ")";
  os.flush();

  m_nameCache.insert({decl->getID(), s});

  return s;
}

} // namespace vf