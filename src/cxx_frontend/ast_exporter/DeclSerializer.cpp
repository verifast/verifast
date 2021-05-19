#include "AstSerializer.h"
#include "clang/AST/Decl.h"

namespace vf {

// TODO: check how to retrieve the name of a decl in a proper way
bool DeclSerializer::visitFunc(stubs::Decl::Function::Builder &builder,
                               const clang::FunctionDecl *decl) {
  auto ser = getSerializer();
  builder.setName(decl->getQualifiedNameAsString());
  builder.setMangledName(ser->getMangledFunc(decl).str());
  auto result = builder.initResult();
  auto returnRange = decl->getReturnTypeSourceRange();
  if (returnRange.isInvalid()) {
    // Try to recover from using an invalid range which will result in a
    // seg-fault. E.g. when handling a conversion function which does not have a
    // return type range.
    returnRange = decl->getSourceRange();
  }
  ser->serializeTypeWithRange(result, decl->getReturnType().getTypePtr(),
                              returnRange);
  auto params = builder.initParams(decl->param_size());
  size_t i(0);
  for (auto p : decl->parameters()) {
    auto param = params[i++];

    param.setName(p->getDeclName().getAsString());
    auto type = param.initType();
    ser->serializeTypeLoc(type, p->getTypeSourceInfo()->getTypeLoc());

    if (p->hasDefaultArg()) {
      auto def = param.initDefault();
      ser->serializeExpr(def, p->getDefaultArg());
    }
  }

  std::list<Annotation> anns;
  if (decl->isThisDeclarationADefinition()) {
    ser->getAnnStore().getContract(decl->getBeginLoc(), anns,
                                   getSourceManager(),
                                   decl->getBody()->getBeginLoc());
  } else {
    ser->getAnnStore().getContract(decl->getBeginLoc(), anns,
                                   getSourceManager());
  }

  auto contractBuilder = builder.initContract(anns.size());
  i = 0;
  for (auto &ann : anns) {
    auto annBuilder = contractBuilder[i++];
    ser->serializeAnnotationClause(annBuilder, ann);
  }

  if (decl->isThisDeclarationADefinition()) {
    auto body = builder.initBody();
    ser->serializeStmt(body, decl->getBody());
  }
  return true;
}

bool DeclSerializer::VisitFunctionDecl(const clang::FunctionDecl *decl) {
  auto function = _builder.initFunction();
  return visitFunc(function, decl);
}

bool DeclSerializer::VisitEmptyDecl(const clang::EmptyDecl *decl) {
  _builder.setEmpty();
  return true;
}

bool DeclSerializer::VisitVarDecl(const clang::VarDecl *decl) {
  auto var = _builder.initVar();
  var.setName(decl->getQualifiedNameAsString());

  auto ty = var.initType();
  getSerializer()->serializeTypeWithRange(
      ty, decl->getType().getTypePtr(),
      {decl->getTypeSpecStartLoc(), decl->getTypeSpecEndLoc()});

  if (decl->hasInit()) {
    auto init = var.initInit();
    auto initExpr = init.initInit();
    getSerializer()->serializeExpr(initExpr, decl->getInit());

#define CASE_INIT(CLANG_STYLE, STUBS_STYLE)                                    \
  case clang::VarDecl::InitializationStyle::CLANG_STYLE:                       \
    init.setStyle(stubs::Decl::Var::InitStyle::STUBS_STYLE);                   \
    break;

    switch (decl->getInitStyle()) {
      CASE_INIT(CInit, C_INIT)
      CASE_INIT(CallInit, CALL_INIT)
      CASE_INIT(ListInit, LIST_INIT)
    }

#undef CASE_INIT
  }
  return true;
}

bool DeclSerializer::VisitFieldDecl(const clang::FieldDecl *decl) {
  auto field = _builder.initField();
  field.setName(decl->getDeclName().getAsString());

  auto ser = getSerializer();
  auto ty = field.initType();
  ser->serializeTypeLoc(ty, decl->getTypeSourceInfo()->getTypeLoc());

  if (decl->hasInClassInitializer()) {
    auto init = field.initInit();
    auto initExpr = init.initInit();
    ser->serializeExpr(initExpr, decl->getInClassInitializer());

#define CASE_INIT(CLANG_STYLE, STUBS_STYLE)                                    \
  case clang::InClassInitStyle::ICIS_##CLANG_STYLE:                            \
    init.setStyle(stubs::Decl::Field::InitStyle::STUBS_STYLE);                 \
    break;

    switch (decl->getInClassInitStyle()) {
      CASE_INIT(CopyInit, COPY_INIT)
      CASE_INIT(ListInit, LIST_INIT)
    default:
      llvm_unreachable(
          "A field with an in-class-initializer should have an init style.");
    }
  }

  return true;
}

bool DeclSerializer::VisitCXXRecordDecl(const clang::CXXRecordDecl *decl) {
  auto rec = _builder.initRecord();

  rec.setName(decl->getQualifiedNameAsString());

  auto kind = decl->isUnion()   ? stubs::RecordKind::UNIO
              : decl->isClass() ? stubs::RecordKind::CLASS
                                : stubs::RecordKind::STRUC;
  rec.setKind(kind);

  bool hasDef(decl->hasDefinition());
  rec.setHasDef(hasDef);

  if (hasDef) {
    using DeclNodeOrphan = NodeOrphan<stubs::Decl>;
    auto orphanage = capnp::Orphanage::getForMessageContaining(_builder);
    llvm::SmallVector<DeclNodeOrphan, 4> fieldOrphans;
    llvm::SmallVector<DeclNodeOrphan, 4> methOrphans;
    llvm::SmallVector<DeclNodeOrphan, 4> declOrphans;

    auto ser = getSerializer();
    for (auto d : decl->decls()) {
      switch (d->getKind()) {
      case clang::Decl::Kind::CXXMethod:
        ser->serializeToOrphan(d, orphanage, methOrphans);
        break;
      case clang::Decl::Kind::Field:
        ser->serializeToOrphan(d, orphanage, fieldOrphans);
        break;
      default:
        if (!d->isImplicit()) {
          ser->serializeToOrphan(d, orphanage, declOrphans);
        }
      }
    }

    auto fields = rec.initFields(fieldOrphans.size());
    auto meths = rec.initMethods(methOrphans.size());
    auto decls = rec.initDecls(declOrphans.size());

    AstSerializer::adoptOrphansToListBuilder(fieldOrphans, fields);
    AstSerializer::adoptOrphansToListBuilder(methOrphans, meths);
    AstSerializer::adoptOrphansToListBuilder(declOrphans, decls);
  }

  return true;
}

bool DeclSerializer::VisitCXXMethodDecl(const clang::CXXMethodDecl *decl) {
  auto meth = _builder.initMethod();
  auto isStatic = decl->isStatic();

  meth.setStatic(isStatic);

  if (!isStatic) {
    auto thisType = meth.initThis();
    getSerializer()->serializeType(thisType,
                                   decl->getThisObjectType().getTypePtr());
  }

  auto func = meth.initFunc();

  return visitFunc(func, decl);
}

bool DeclSerializer::VisitCXXConstructorDecl(
    const clang::CXXConstructorDecl *decl) {
  _builder.setDefConstructor();
  return decl->isImplicit();
}

bool DeclSerializer::VisitCXXDestructorDecl(
    const clang::CXXDestructorDecl *decl) {
  _builder.setDefDestructor();
  return decl->isImplicit();
}

bool DeclSerializer::VisitAccessSpecDecl(const clang::AccessSpecDecl *decl) {
  _builder.setAccessSpec();
  return true;
}

bool DeclSerializer::VisitTypedefNameDecl(const clang::TypedefNameDecl *decl) {
  auto def = _builder.initTypedef();
  def.setName(decl->getQualifiedNameAsString());

  auto defType = def.initType();
  getSerializer()->serializeTypeLoc(defType,
                                    decl->getTypeSourceInfo()->getTypeLoc());

  return true;
}

bool DeclSerializer::VisitEnumDecl(const clang::EnumDecl *decl) {
  auto enumDecl = _builder.initEnumDecl();
  enumDecl.setName(decl->getQualifiedNameAsString());

  auto nbFields =
      std::distance(decl->enumerator_begin(), decl->enumerator_end());
  auto fields = enumDecl.initFields(nbFields);

  size_t i(0);
  for (auto field : decl->enumerators()) {
    auto enumField = fields[i++];
    enumField.setName(field->getDeclName().getAsString());
    if (auto init = field->getInitExpr()) {
      auto fieldExpr = enumField.initExpr();
      getSerializer()->serializeExpr(fieldExpr, init);
    }
  }

  return true;
}

} // namespace vf