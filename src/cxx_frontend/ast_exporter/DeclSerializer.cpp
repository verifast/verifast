#include "AstSerializer.h"
#include "FixedWidthInt.h"
#include "clang/AST/Decl.h"

namespace vf {

// TODO: check how to retrieve the name of a decl in a proper way
void DeclSerializer::serializeFuncDecl(stubs::Decl::Function::Builder &builder,
                                       const clang::FunctionDecl *decl,
                                       llvm::StringRef mangledName) {
  builder.setName(decl->getQualifiedNameAsString());
  builder.setMangledName(mangledName.str());
  auto result = builder.initResult();
  m_serializer.serializeTypeLoc(result,
                                decl->getFunctionTypeLoc().getReturnLoc());

  auto paramsBuilder = builder.initParams(decl->param_size());
  m_serializer.serializeParams(paramsBuilder, decl->parameters());

  auto isImplicit = decl->isImplicit();
  auto isDef = decl->isThisDeclarationADefinition();

  // Implicit functions cannot have annotations provided by the programmer.
  if (!isImplicit) {
    llvm::SmallVector<Annotation> anns;
    m_serializer.getAnnStore().getContract(decl, anns, getSourceManager());
    auto contractBuilder = builder.initContract(anns.size());
    m_serializer.serializeAnnotationClauses(contractBuilder, anns);
  }

  // Implicit functions have a definition, but only have a body when
  // they are referenced. The body is always a compound empty statement.
  // Therefore, we always serialize them as a declaration without body.
  if (!isImplicit && isDef) {
    auto body = builder.initBody();
    m_serializer.serializeStmt(body, decl->getBody());
  }
}

bool DeclSerializer::VisitFunctionDecl(const clang::FunctionDecl *decl) {
  auto function = m_builder.initFunction();
  serializeFuncDecl(function, decl, m_serializer.getMangledFunc(decl));
  return true;
}

bool DeclSerializer::VisitEmptyDecl(const clang::EmptyDecl *decl) {
  m_builder.setEmpty();
  return true;
}

bool DeclSerializer::VisitVarDecl(const clang::VarDecl *decl) {
  auto var = m_builder.initVar();
  var.setName(decl->getQualifiedNameAsString());

  auto ty = var.initType();
  m_serializer.serializeTypeLoc(ty, decl->getTypeSourceInfo()->getTypeLoc());

  if (decl->hasInit()) {
    auto init = var.initInit();
    auto initExpr = init.initInit();
    m_serializer.serializeExpr(initExpr, decl->getInit());

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

  auto ty = builder.initType();
  m_serializer.serializeTypeLoc(ty, decl->getTypeSourceInfo()->getTypeLoc());

  if (decl->hasInClassInitializer()) {
    auto init = builder.initInit();
    auto initExpr = init.initInit();
    m_serializer.serializeExpr(initExpr, decl->getInClassInitializer());

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
  auto field = m_builder.initField();
  serializeFieldDecl(field, decl);
  return true;
}

void DeclSerializer::serializeBases(
    capnp::List<stubs::Node<stubs::Decl::Record::BaseSpec>,
                capnp::Kind::STRUCT>::Builder &builder,
    clang::CXXRecordDecl::base_class_const_range bases) {
  size_t i(0);
  for (auto base : bases) {
    auto baseTypePtr = base.getType().getTypePtr();
    auto baseDecl = baseTypePtr->getAsRecordDecl();
    auto locBuilder = builder[i].initLoc();
    auto descBuilder = builder[i].initDesc();

    serializeSrcRange(locBuilder, base.getBaseTypeLoc(), getSourceManager());
    descBuilder.setName(baseDecl->getQualifiedNameAsString());
    descBuilder.setVirtual(base.isVirtual());

    ++i;
  }
}

using DeclNodeOrphan = NodeOrphan<stubs::Decl>;
bool DeclSerializer::VisitCXXRecordDecl(const clang::CXXRecordDecl *decl) {
  auto rec = m_builder.initRecord();

  rec.setName(decl->getQualifiedNameAsString());

  auto kind = decl->isUnion()   ? stubs::RecordKind::UNIO
              : decl->isClass() ? stubs::RecordKind::CLASS
                                : stubs::RecordKind::STRUC;
  rec.setKind(kind);

  if (decl->hasDefinition()) {
    auto orphanage = capnp::Orphanage::getForMessageContaining(m_builder);
    llvm::SmallVector<DeclNodeOrphan> declNodeOrphans;
    auto &store = m_serializer.getAnnStore();
    auto &SM = getSourceManager();
    llvm::SmallVector<Annotation> anns;

    for (auto d : decl->decls()) {
      if (d->isImplicit() && !m_serializeImplicitDecls)
        continue;

      store.getUntilLoc(anns, d->getBeginLoc(), SM);
      m_serializer.serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);
      m_serializer.serializeToOrphan(d, orphanage, declNodeOrphans);
      anns.clear();
    }

    store.getUntilLoc(anns, decl->getBraceRange().getEnd(), SM);
    m_serializer.serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);

    auto body = rec.initBody();
    body.setPolymorphic(decl->isPolymorphic());
    auto basesBuilder = body.initBases(decl->getNumBases());
    serializeBases(basesBuilder, decl->bases());

    auto declsBuilder = body.initDecls(declNodeOrphans.size());
    AstSerializer::adoptOrphansToListBuilder(declNodeOrphans, declsBuilder);
  }
  return true;
}

void DeclSerializer::serializeMethodDecl(stubs::Decl::Method::Builder &builder,
                                         const clang::CXXMethodDecl *decl,
                                         llvm::StringRef mangledName) {
  auto isStatic = decl->isStatic();
  builder.setStatic(isStatic);
  builder.setImplicit(decl->isImplicit());
  if (!isStatic) {
    auto thisType = builder.initThis();
    m_serializer.serializeQualType(thisType, decl->getThisObjectType());
  }

  auto func = builder.initFunc();
  serializeFuncDecl(func, decl, mangledName);
}

bool DeclSerializer::VisitCXXMethodDecl(const clang::CXXMethodDecl *decl) {
  auto meth = m_builder.initMethod();
  serializeMethodDecl(meth, decl, m_serializer.getMangledFunc(decl));
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
  auto ctor = m_builder.initCtor();
  // nb inits will be 1 if it delegates to another ctor
  auto initBuilders = ctor.initInitList(decl->getNumCtorInitializers());

  size_t i(0);
  for (auto init : decl->inits()) {
    auto initBuilder = initBuilders[i++];
    initBuilder.setName(init->isMemberInitializer()
                            ? init->getMember()->getNameAsString()
                            : "this");
    initBuilder.setIsWritten(init->isWritten());
    auto *initExpr = init->getInit();
    if (!llvm::isa<clang::CXXDefaultInitExpr>(initExpr)) {
      auto exprBuilder = initBuilder.initInit();
      m_serializer.serializeExpr(exprBuilder, init->getInit());
    }
  }

  auto meth = ctor.initMethod();
  serializeMethodDecl(meth, decl, m_serializer.getMangledCtorName(decl));

  auto parent = ctor.initParent();
  serializeRecordRef(parent, decl->getParent());

  return true;
}

bool DeclSerializer::VisitCXXDestructorDecl(
    const clang::CXXDestructorDecl *decl) {
  auto dtor = m_builder.initDtor();

  auto meth = dtor.initMethod();
  serializeMethodDecl(meth, decl, m_serializer.getMangledDtorName(decl));

  auto parent = dtor.initParent();
  serializeRecordRef(parent, decl->getParent());
  return true;
}

bool DeclSerializer::VisitAccessSpecDecl(const clang::AccessSpecDecl *decl) {
  m_builder.setAccessSpec();
  return true;
}

bool DeclSerializer::VisitTypedefNameDecl(const clang::TypedefNameDecl *decl) {
  auto def = m_builder.initTypedef();
  def.setName(decl->getQualifiedNameAsString());

  auto defType = def.initType();
  auto typeLoc = decl->getTypeSourceInfo()->getTypeLoc();

  auto typeExpandsFromSystemMacro =
      getSourceManager().isInSystemMacro(typeLoc.getBeginLoc());

  if (!typeExpandsFromSystemMacro) {
    m_serializer.serializeTypeLoc(defType, typeLoc);
    return true;
  }

  if (auto fwi = getFixedWidthFromString(decl->getName())) {
    auto locBuilder = defType.initLoc();
    auto descBuilder = defType.initDesc();

    serializeSrcRange(locBuilder, typeLoc.getSourceRange(), getSourceManager());

    auto fw = descBuilder.initFixedWidth();
    fw.setKind(fwi->isSigned ? stubs::Type::FixedWidth::FixedWidthKind::INT
                             : stubs::Type::FixedWidth::FixedWidthKind::U_INT);
    fw.setBits(fwi->bits);
    return true;
  }

  m_serializer.serializeTypeLoc(defType, typeLoc);
  return true;
}

bool DeclSerializer::VisitEnumDecl(const clang::EnumDecl *decl) {
  auto enumDecl = m_builder.initEnumDecl();
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
      m_serializer.serializeExpr(fieldExpr, init);
    }
  }

  return true;
}

bool DeclSerializer::VisitNamespaceDecl(const clang::NamespaceDecl *decl) {
  auto ns = m_builder.initNamespace();
  ns.setName(decl->getNameAsString());

  auto orphanage = capnp::Orphanage::getForMessageContaining(m_builder);
  llvm::SmallVector<DeclNodeOrphan, 16> declNodeOrphans;
  auto &store = m_serializer.getAnnStore();
  auto &SM = getSourceManager();
  llvm::SmallVector<Annotation> anns;

  for (auto d : decl->decls()) {
    if (d->isImplicit() && !m_serializeImplicitDecls)
      continue;

    store.getUntilLoc(anns, d->getBeginLoc(), SM);
    m_serializer.serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);
    m_serializer.serializeToOrphan(d, orphanage, declNodeOrphans);
    anns.clear();
  }

  store.getUntilLoc(anns, decl->getRBraceLoc(), SM);
  m_serializer.serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);

  auto decls = ns.initDecls(declNodeOrphans.size());
  AstSerializer::adoptOrphansToListBuilder(declNodeOrphans, decls);

  return true;
}

} // namespace vf