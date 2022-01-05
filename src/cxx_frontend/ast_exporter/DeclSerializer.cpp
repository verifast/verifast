#include "AstSerializer.h"
#include "clang/AST/Decl.h"

namespace vf {

void DeclSerializer::serializeParams(
    capnp::List<stubs::Decl::Param, capnp::Kind::STRUCT>::Builder &builder,
    llvm::ArrayRef<clang::ParmVarDecl *> params) {
  auto ser = getSerializer();
  size_t i(0);
  for (auto p : params) {
    auto param = builder[i++];

    auto declName = p->getDeclName();
    param.setName(declName.getAsString());
    auto type = param.initType();
    auto typeInfo = p->getTypeSourceInfo();
    if (typeInfo) {
      ser->serializeTypeLoc(type, typeInfo->getTypeLoc());
    } else {
      ser->serializeTypeWithRange(type, p->getType().getTypePtr(), {});
    }
    if (p->hasDefaultArg()) {
      auto def = param.initDefault();
      ser->serializeExpr(def, p->getDefaultArg());
    }
  }
}

// TODO: check how to retrieve the name of a decl in a proper way
void DeclSerializer::serializeFuncDecl(stubs::Decl::Function::Builder &builder,
                                       const clang::FunctionDecl *decl,
                                       llvm::StringRef mangledName) {
  auto ser = getSerializer();
  builder.setName(decl->getQualifiedNameAsString());
  builder.setMangledName(mangledName.str());
  auto result = builder.initResult();
  auto returnRange = decl->getReturnTypeSourceRange();

  ser->serializeTypeWithRange(result, decl->getReturnType().getTypePtr(),
                              returnRange);

  auto paramsBuilder = builder.initParams(decl->param_size());
  serializeParams(paramsBuilder, decl->parameters());
  std::list<Annotation> anns;

  auto isImplicit = decl->isImplicit();
  auto isDef = decl->isThisDeclarationADefinition();

  // Implicit functions cannot have annotations provided by the programmer.
  if (!isImplicit) {
    if (isDef) {
      ser->getAnnStore().getContract(decl->getBeginLoc(), anns,
                                     getSourceManager(),
                                     decl->getBody()->getBeginLoc());
    } else {
      ser->getAnnStore().getContract(decl->getBeginLoc(), anns,
                                     getSourceManager());
    }
    auto contractBuilder = builder.initContract(anns.size());
    size_t i(0);
    for (auto &ann : anns) {
      auto annBuilder = contractBuilder[i++];
      ser->serializeAnnotationClause(annBuilder, ann);
    }
  }

  // Implicit functions have a definition, but only have a body when
  // they are referenced. The body is always a compound empty statement.
  // Therefore, we always serialize them as a declaration without body.
  if (!isImplicit && isDef) {
    auto body = builder.initBody();
    ser->serializeStmt(body, decl->getBody());
  }
}

bool DeclSerializer::VisitFunctionDecl(const clang::FunctionDecl *decl) {
  auto function = _builder.initFunction();
  serializeFuncDecl(function, decl, getSerializer()->getMangledFunc(decl));
  return true;
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

void DeclSerializer::serializeFieldDecl(stubs::Decl::Field::Builder &builder,
                                        const clang::FieldDecl *decl) {
  builder.setName(decl->getDeclName().getAsString());

  auto ser = getSerializer();
  auto ty = builder.initType();
  ser->serializeTypeLoc(ty, decl->getTypeSourceInfo()->getTypeLoc());

  if (decl->hasInClassInitializer()) {
    auto init = builder.initInit();
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
}

bool DeclSerializer::VisitFieldDecl(const clang::FieldDecl *decl) {
  auto field = _builder.initField();
  serializeFieldDecl(field, decl);
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
  if (hasDef) {
    size_t nbFields(0);
    size_t nbDecls(0);

    for (auto d : decl->decls()) {
      if (llvm::isa<clang::FieldDecl>(d)) {
        ++nbFields;
      } else {
        ++nbDecls;
      }
    }

    auto body = rec.initBody();
    auto fieldsBuilder = body.initFields(nbFields);
    auto declsBuilder = body.initDecls(nbDecls);
    nbFields = 0;
    nbDecls = 0;

    auto ser = getSerializer();

    for (auto d : decl->decls()) {
      if (auto *field = llvm::dyn_cast<clang::FieldDecl>(d)) {
        auto builder = fieldsBuilder[nbFields++];
        auto locBuilder = builder.initLoc();
        auto descBuilder = builder.initDesc();
        serializeSrcRange(locBuilder, d->getSourceRange(), getSourceManager());
        serializeFieldDecl(descBuilder, field);
      } else {
        auto builder = declsBuilder[nbDecls++];
        ser->serializeDecl(builder, d);
      }
    }
  }

  return true;
}

void DeclSerializer::serializeMethodDecl(stubs::Decl::Method::Builder &builder,
                                         const clang::CXXMethodDecl *decl,
                                         llvm::StringRef mangledName) {
  auto isStatic = decl->isStatic();
  builder.setStatic(isStatic);
  auto ser = getSerializer();
  if (!isStatic) {
    auto thisType = builder.initThis();
    getSerializer()->serializeType(thisType,
                                   decl->getThisObjectType().getTypePtr());
  }

  auto func = builder.initFunc();
  serializeFuncDecl(func, decl, mangledName);
}

bool DeclSerializer::VisitCXXMethodDecl(const clang::CXXMethodDecl *decl) {
  auto meth = _builder.initMethod();
  serializeMethodDecl(meth, decl, getSerializer()->getMangledFunc(decl));
  return true;
}

void serializeRecordRef(stubs::RecordRef::Builder &builder,
                        const clang::CXXRecordDecl *record) {
  builder.setName(record->getQualifiedNameAsString());
  builder.setKind(record->isStruct()  ? stubs::RecordKind::STRUC
                  : record->isClass() ? stubs::RecordKind::CLASS
                                      : stubs::RecordKind::UNIO);
}

bool DeclSerializer::VisitCXXConstructorDecl(
    const clang::CXXConstructorDecl *decl) {
  auto ctor = _builder.initCtor();
  auto ser = getSerializer();
  ctor.setImplicit(decl->isImplicit());
  auto initBuilders = ctor.initInitList(decl->getNumCtorInitializers());

  size_t i(0);
  for (auto init : decl->inits()) {
    auto initBuilder = initBuilders[i++];
    initBuilder.setName(init->getMember()->getNameAsString());
    initBuilder.setIsWritten(init->isWritten());
    
    auto *initExpr = init->getInit();
    if (! llvm::isa<clang::CXXDefaultInitExpr>(initExpr)) {
      auto exprBuilder = initBuilder.initInit();
      ser->serializeExpr(exprBuilder, init->getInit());
    }
  }

  auto meth = ctor.initMethod();
  serializeMethodDecl(meth, decl, ser->getMangledCtorName(decl));

  auto parent = ctor.initParent();
  serializeRecordRef(parent, decl->getParent());

  return true;
}

bool DeclSerializer::VisitCXXDestructorDecl(
    const clang::CXXDestructorDecl *decl) {
  // builder.setImplicit(decl->isImplicit());
  // auto methodBuilder = builder.initMethod();
  // serializeMethodDecl(methodBuilder, decl,
  // getSerializer()->getMangledDtorName(decl));
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