#include "DeclSerializer.h"
#include "FixedWidthInt.h"
#include "Location.h"
#include "NodeListSerializer.h"
#include "clang/AST/CXXInheritance.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/ExprCXX.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Lex/Lexer.h"

namespace vf {

namespace {

struct DeclSerializerImpl
    : public clang::ConstDeclVisitor<DeclSerializerImpl, bool> {

  void serializeFieldDecl(stubs::Decl::Field::Builder builder,
                          const clang::FieldDecl *decl) {
    builder.setName(decl->getDeclName().getAsString());

    TypeNodeBuilder typeBuilder = builder.initType();
    m_ASTSerializer->serialize(typeBuilder,
                               decl->getTypeSourceInfo()->getTypeLoc());

    if (decl->hasInClassInitializer()) {
      stubs::Decl::Field::FieldInit::Builder initBuilder = builder.initInit();
      ExprNodeBuilder initExprBuilder = initBuilder.initInit();
      m_ASTSerializer->serialize(initExprBuilder,
                                 decl->getInClassInitializer());

#define CASE_INIT(CLANG_STYLE, STUBS_STYLE)                                    \
  case clang::InClassInitStyle::ICIS_##CLANG_STYLE:                            \
    initBuilder.setStyle(stubs::Decl::Field::InitStyle::STUBS_STYLE);          \
    break;

      switch (decl->getInClassInitStyle()) {
        CASE_INIT(CopyInit, COPY_INIT)
        CASE_INIT(ListInit, LIST_INIT)
      default:
        llvm_unreachable(
            "A field with an in-class-initializer should have an init style.");
      }
    }
#undef CASE_INIT
  }

  void serializeFunctionDecl(stubs::Decl::Function::Builder functionBuilder,
                             const clang::FunctionDecl *decl,
                             bool serializeContract) {
    std::string name = m_ASTSerializer->getQualifiedFuncName(decl);
    clang::FunctionTypeLoc returnTypeLoc = decl->getFunctionTypeLoc();
    bool isImplicit = decl->isImplicit();
    bool isDef = decl->isThisDeclarationADefinition();

    TypeNodeBuilder resultBuilder = functionBuilder.initResult();
    ListBuilder<stubs::Param> paramBuilder =
        functionBuilder.initParams(decl->param_size());

    functionBuilder.setName(name.data());
    functionBuilder.setIsMain(decl->isMain());

    if (!returnTypeLoc.isNull()) {
      m_ASTSerializer->serialize(resultBuilder, returnTypeLoc.getReturnLoc());
    } else {
      stubs::Type::Builder resultTypeBuilder = resultBuilder.initDesc();
      m_ASTSerializer->serialize(resultTypeBuilder, decl->getReturnType());
    }

    m_ASTSerializer->serialize(paramBuilder, decl->parameters());

    // Implicit function do not have a contract and do not have a body. Clang
    // generates an empty function body for implicit function if they are
    // referenced. We do not serialize this empty body.
    if (isImplicit) {
      return;
    }

    if (serializeContract) {
      AnnotationsRef contract =
          m_ASTSerializer->getAnnotationManager().getContract(decl);
      ListBuilder<stubs::Clause> contractBuilder =
          functionBuilder.initContract(contract.size());
      m_ASTSerializer->serialize(contractBuilder, contract);
    }

    if (isDef) {
      assert(decl->doesThisDeclarationHaveABody());

      StmtNodeBuilder bodyBuilder = functionBuilder.initBody();
      m_ASTSerializer->serialize(bodyBuilder, decl->getBody());
    }
  }

  void serializeRecordRef(stubs::RecordRef::Builder builder,
                          const clang::CXXRecordDecl *record) {
    builder.setName(record->getQualifiedNameAsString());
    builder.setKind(record->isStruct()  ? stubs::RecordKind::STRUC
                    : record->isClass() ? stubs::RecordKind::CLASS
                                        : stubs::RecordKind::UNIO);
  }

  void serializeBases(
      ListBuilder<stubs::Node<stubs::Decl::Record::BaseSpec>> builder,
      clang::CXXRecordDecl::base_class_const_range bases) {
    size_t i(0);
    for (auto base : bases) {
      const clang::Type *baseTypePtr = base.getType().getTypePtr();
      const clang::RecordDecl *baseDecl = baseTypePtr->getAsRecordDecl();
      LocBuilder locBuilder = builder[i].initLoc();
      stubs::Decl::Record::BaseSpec::Builder descBuilder =
          builder[i].initDesc();

      m_ASTSerializer->serialize(locBuilder, base.getBaseTypeLoc());
      descBuilder.setName(baseDecl->getQualifiedNameAsString());
      descBuilder.setVirtual(base.isVirtual());

      ++i;
    }
  }

  void serializeMethodDecl(stubs::Decl::Method::Builder builder,
                           const clang::CXXMethodDecl *decl) {
    bool isStatic = decl->isStatic();
    builder.setStatic(isStatic);

    bool isVirtual(decl->isVirtual());
    builder.setVirtual(isVirtual);

    if (isVirtual) {
      ListBuilder<stubs::Decl::Method::Override> overriddenMethsBuilder =
          builder.initOverrides(decl->size_overridden_methods());
      size_t i(0);
      for (const clang::CXXMethodDecl *meth : decl->overridden_methods()) {
        const clang::CXXRecordDecl *parentRecord =
            llvm::dyn_cast<clang::CXXRecordDecl>(
                meth->getFirstDecl()->getParent());
        stubs::Decl::Method::Override::Builder overrideBuilder =
            overriddenMethsBuilder[i++];
        overrideBuilder.setName(m_ASTSerializer->getQualifiedFuncName(meth));
        stubs::RecordRef::Builder base = overrideBuilder.initBase();
        serializeRecordRef(base, parentRecord);
      }
    }

    if (!isStatic) {
      m_ASTSerializer->serialize(builder.initThis(), decl->getThisObjectType());
    }
    serializeFunctionDecl(builder.initFunc(), decl, true);
  }

  bool checkDefaultedOrDeleted(clang::CXXMethodDecl const * const decl) {
    if(decl->isDeleted()) {
      // Regarding deleted virtual functions the C++17 standard says "A function
      // with a deleted definition shall not override a function that does not
      // have a deleted definition." and vice versa. Thus a deleted function that
      // is virtual behaves the same as if it was not virtual.

      m_builder.setDeleted();

      return true;
    }
    else if(decl->isDefaulted()) {
      clang::DiagnosticsEngine &diagsEngine =
        m_ASTSerializer->getASTContext().getDiagnostics();
      unsigned id = diagsEngine.getCustomDiagID(
        clang::DiagnosticsEngine::Error,
        "Declaration of defaulted method function is not supported.");
      diagsEngine.Report(decl->getBeginLoc(), id);

      return true;
    }

    return false;
  }

  bool VisitFunctionDecl(const clang::FunctionDecl *decl) {
    serializeFunctionDecl(m_builder.initFunction(), decl, true);
    return true;
  }

  bool VisitEmptyDecl(const clang::EmptyDecl *decl) {
    m_builder.setEmpty();
    return true;
  }

  bool VisitVarDecl(const clang::VarDecl *decl) {
    stubs::Decl::Var::Builder varBuilder = m_builder.initVar();
    TypeNodeBuilder typeBuilder = varBuilder.initType();

    varBuilder.setName(decl->getQualifiedNameAsString());
    m_ASTSerializer->serialize(typeBuilder,
                               decl->getTypeSourceInfo()->getTypeLoc());

    if (decl->hasInit()) {
      stubs::Decl::Var::VarInit::Builder varInitBuilder = varBuilder.initInit();
      ExprNodeBuilder initExpr = varInitBuilder.initInit();
      m_ASTSerializer->serialize(initExpr, decl->getInit());

#define CASE_INIT(CLANG_STYLE, STUBS_STYLE)                                    \
  case clang::VarDecl::InitializationStyle::CLANG_STYLE:                       \
    varInitBuilder.setStyle(stubs::Decl::Var::InitStyle::STUBS_STYLE);         \
    break;

      switch (decl->getInitStyle()) {
        CASE_INIT(CInit, C_INIT)
        CASE_INIT(CallInit, CALL_INIT)
        CASE_INIT(ListInit, LIST_INIT)
      case clang::VarDecl::InitializationStyle::ParenListInit: {
        clang::DiagnosticsEngine &diagsEngine =
            m_ASTSerializer->getASTContext().getDiagnostics();
        unsigned id = diagsEngine.getCustomDiagID(
            clang::DiagnosticsEngine::Error,
            "Parenthesized list-initialization is not supported");
        diagsEngine.Report(decl->getBeginLoc(), id);
      }
      }

#undef CASE_INIT
    }
    return true;
  }

  bool VisitFieldDecl(const clang::FieldDecl *decl) {
    stubs::Decl::Field::Builder fieldBuilder = m_builder.initField();
    serializeFieldDecl(fieldBuilder, decl);
    return true;
  }

  void serializeContext(const clang::DeclContext *context,
                        clang::SourceRange range,
                        DeclListSerializer &serializer) {
    clang::SourceLocation beginLoc = range.getBegin();
    for (const clang::Decl *decl : context->decls()) {
      if (decl->isImplicit() && m_ASTSerializer->skipImplicitDecls()) {
        continue;
      }

      AnnotationsRef annotations =
          m_ASTSerializer->getAnnotationManager()
              .getInRange(beginLoc, decl->getBeginLoc())
              .drop_while(
                  Annotation::Predicate<Annotation::Ann_ContractClause>());
      serializer << annotations << decl;
      beginLoc = decl->getEndLoc();
    }

    AnnotationsRef annotations =
        m_ASTSerializer->getAnnotationManager()
            .getInRange(beginLoc, range.getEnd())
            .drop_while(
                Annotation::Predicate<Annotation::Ann_ContractClause>());
    serializer << annotations;
  }

  bool VisitCXXRecordDecl(const clang::CXXRecordDecl *decl) {
    stubs::Decl::Record::Builder recordBuilder = m_builder.initRecord();

    recordBuilder.setName(decl->getQualifiedNameAsString());

    stubs::RecordKind kind = decl->isUnion()   ? stubs::RecordKind::UNIO
                             : decl->isClass() ? stubs::RecordKind::CLASS
                                               : stubs::RecordKind::STRUC;
    recordBuilder.setKind(kind);
    if (decl->isThisDeclarationADefinition()) {
      capnp::Orphanage orphanage =
          capnp::Orphanage::getForMessageContaining(m_builder);

      DeclListSerializer declListSerializer(orphanage,
                                            DeclSerializer(*m_ASTSerializer));
      serializeContext(decl, decl->getBraceRange(), declListSerializer);

      stubs::Decl::Record::Body::Builder bodyBuilder = recordBuilder.initBody();
      bodyBuilder.setPolymorphic(decl->isPolymorphic());
      ListBuilder<stubs::Node<stubs::Decl::Record::BaseSpec>> basesBuilder =
          bodyBuilder.initBases(decl->getNumBases());
      serializeBases(basesBuilder, decl->bases());

      clang::CXXFinalOverriderMap finalOverrides;
      decl->getFinalOverriders(finalOverrides);
      bodyBuilder.setIsAbstract(decl->isAbstract());

      finalOverrides.remove_if(
          [decl](
              std::pair<const clang::CXXMethodDecl *, clang::OverridingMethods>
                  p) {
            clang::OverridingMethods overridingMeths = p.second;
            for (auto it = overridingMeths.begin(); it < overridingMeths.end();
                 ++it) {
              llvm::ArrayRef<clang::UniqueVirtualMethod> overrides = it->second;
              for (const clang::UniqueVirtualMethod &override : overrides) {
                if (override.Method->getParent() != decl)
                  return false;
              }
            }
            return true;
          });

      capnp::List<capnp::Text, capnp::Kind::BLOB>::Builder
          nonOverriddenMethsBuilder =
              bodyBuilder.initNonOverriddenMethods(finalOverrides.size());
      size_t i(0);
      for (auto finalOverride : finalOverrides) {
        nonOverriddenMethsBuilder.set(
            i++, m_ASTSerializer->getQualifiedFuncName(finalOverride.first));
      }

      ListBuilder<stubs::Node<stubs::Decl>> declsBuilder =
          bodyBuilder.initDecls(declListSerializer.size());
      declListSerializer.adoptToListBuilder(declsBuilder);
    }
    return true;
  }

  bool VisitCXXMethodDecl(const clang::CXXMethodDecl *decl) {
    // Serialize method only if it is not defaulted or deleted
    // and create error when necessary
    if(checkDefaultedOrDeleted(decl)) return true;

    stubs::Decl::Method::Builder methodBuilder = m_builder.initMethod();
    serializeMethodDecl(methodBuilder, decl);
    return true;
  }

  bool VisitCXXConstructorDecl(const clang::CXXConstructorDecl *decl) {
    // Serialize constructor only if it is not defaulted or deleted
    // and create error when necessary
    if(checkDefaultedOrDeleted(decl)) return true;

    stubs::Decl::Ctor::Builder ctorBuilder = m_builder.initCtor();
    // nb inits will be 1 if it delegates to another ctor
    ListBuilder<stubs::Decl::Ctor::CtorInit> initBuilders =
        ctorBuilder.initInitList(decl->getNumCtorInitializers());

    size_t i(0);
    for (const clang::CXXCtorInitializer *init : decl->inits()) {
      stubs::Decl::Ctor::CtorInit::Builder initBuilder = initBuilders[i++];
      initBuilder.setName(init->isMemberInitializer()
                              ? init->getMember()->getNameAsString()
                              : "this");
      initBuilder.setIsWritten(init->isWritten());
      const clang::Expr *initExpr = init->getInit();
      if (!llvm::isa_and_nonnull<clang::CXXDefaultInitExpr>(initExpr)) {
        auto exprBuilder = initBuilder.initInit();
        m_ASTSerializer->serialize(exprBuilder, init->getInit());
      }
    }

    stubs::Decl::Method::Builder meth = ctorBuilder.initMethod();
    serializeMethodDecl(meth, decl);

    stubs::RecordRef::Builder parent = ctorBuilder.initParent();
    serializeRecordRef(parent, decl->getParent());

    return true;
  }

  bool VisitCXXDestructorDecl(const clang::CXXDestructorDecl *decl) {
    // Serialize destructor only if it is not defaulted or deleted
    // and create error when necessary
    if(checkDefaultedOrDeleted(decl)) return true;

    stubs::Decl::Dtor::Builder dtorBuilder = m_builder.initDtor();

    stubs::Decl::Method::Builder methodBuilder = dtorBuilder.initMethod();
    serializeMethodDecl(methodBuilder, decl);

    stubs::RecordRef::Builder parent = dtorBuilder.initParent();
    serializeRecordRef(parent, decl->getParent());

    return true;
  }

  bool VisitAccessSpecDecl(const clang::AccessSpecDecl *decl) {
    m_builder.setAccessSpec();
    return true;
  }

  bool VisitTypedefNameDecl(const clang::TypedefNameDecl *decl) {
    stubs::Decl::Typedef::Builder typedefBuilder = m_builder.initTypedef();
    typedefBuilder.setName(decl->getQualifiedNameAsString());

    TypeNodeBuilder typeBuilder = typedefBuilder.initType();
    clang::TypeLoc typeLoc = decl->getTypeSourceInfo()->getTypeLoc();

    auto typeExpandsFromSystemMacro =
        m_ASTSerializer->getASTContext().getSourceManager().isInSystemMacro(
            typeLoc.getBeginLoc());

    if (!typeExpandsFromSystemMacro) {
      m_ASTSerializer->serialize(typeBuilder, typeLoc);
      return true;
    }

    if (std::optional<FixedWidthInt> fwi =
            getFixedWidthFromString(decl->getName())) {
      LocBuilder locBuilder = typeBuilder.initLoc();
      stubs::Type::Builder descBuilder = typeBuilder.initDesc();

      m_ASTSerializer->serialize(locBuilder, typeLoc.getSourceRange());

      stubs::Type::FixedWidth::Builder fw = descBuilder.initFixedWidth();
      fw.setKind(fwi->isSigned
                     ? stubs::Type::FixedWidth::FixedWidthKind::INT
                     : stubs::Type::FixedWidth::FixedWidthKind::U_INT);
      fw.setBits(fwi->bits);
      return true;
    }

    m_ASTSerializer->serialize(typeBuilder, typeLoc);
    return true;
  }

  bool VisitEnumDecl(const clang::EnumDecl *decl) {
    stubs::Decl::Enum::Builder enumDeclBuilder = m_builder.initEnumDecl();
    enumDeclBuilder.setName(decl->getQualifiedNameAsString());

    auto nbFields =
        std::distance(decl->enumerator_begin(), decl->enumerator_end());
    ListBuilder<stubs::Decl::Enum::EnumField> fieldsBuilder =
        enumDeclBuilder.initFields(nbFields);

    size_t i(0);
    for (const clang::EnumConstantDecl *field : decl->enumerators()) {
      stubs::Decl::Enum::EnumField::Builder enumFieldBuilder =
          fieldsBuilder[i++];
      enumFieldBuilder.setName(field->getDeclName().getAsString());
      if (const clang::Expr *init = field->getInitExpr()) {
        ExprNodeBuilder fieldExpr = enumFieldBuilder.initExpr();
        m_ASTSerializer->serialize(fieldExpr, init);
      }
    }

    return true;
  }

  bool VisitNamespaceDecl(const clang::NamespaceDecl *decl) {
    stubs::Decl::Namespace::Builder namespaceBuilder =
        m_builder.initNamespace();
    namespaceBuilder.setName(decl->getNameAsString());

    DeclListSerializer declListSerializer(
        capnp::Orphanage::getForMessageContaining(m_builder),
        DeclSerializer(*m_ASTSerializer));

    clang::SourceLocation namespaceNameLoc = decl->getLocation();
    std::optional<clang::Token> lBrace = clang::Lexer::findNextToken(
        namespaceNameLoc, m_ASTSerializer->getASTContext().getSourceManager(),
        m_ASTSerializer->getASTContext().getLangOpts());
    assert(lBrace && "No next token");

    serializeContext(decl, {lBrace->getLocation(), decl->getRBraceLoc()},
                     declListSerializer);
    ListBuilder<stubs::Node<stubs::Decl>> declsBuilder =
        namespaceBuilder.initDecls(declListSerializer.size());
    declListSerializer.adoptToListBuilder(declsBuilder);

    return true;
  }

  bool VisitFunctionTemplateDecl(const clang::FunctionTemplateDecl *decl) {
    stubs::Decl::FunctionTemplate::Builder functionTemplateBuilder =
        m_builder.initFunctionTemplate();
    const clang::FunctionDecl *funcDecl = decl->getTemplatedDecl();
    functionTemplateBuilder.setName(
        m_ASTSerializer->getQualifiedFuncName(funcDecl));

    if (!decl->isImplicit()) {
      AnnotationsRef contract =
          m_ASTSerializer->getAnnotationManager().getContract(funcDecl);
      ListBuilder<stubs::Clause> contractBuilder =
          functionTemplateBuilder.initContract(contract.size());
      m_ASTSerializer->serialize(contractBuilder, contract);
    }

    auto nbSpecs = std::distance(decl->spec_begin(), decl->spec_end());

    size_t i(0);
    ListBuilder<stubs::Node<stubs::Decl::Function>> specsBuilder =
        functionTemplateBuilder.initSpecs(nbSpecs);
    for (const clang::FunctionDecl *spec : decl->specializations()) {
      const clang::FunctionTemplateSpecializationInfo *info =
          spec->getTemplateSpecializationInfo();
      if (info->isExplicitInstantiationOrSpecialization()) {
        auto &diagsEngine = m_ASTSerializer->getASTContext().getDiagnostics();
        auto id = diagsEngine.getCustomDiagID(
            clang::DiagnosticsEngine::Error,
            "Explicit instantiation and specialization is not supported");
        diagsEngine.Report(spec->getBeginLoc(), id);
      }

      NodeBuilder<stubs::Decl::Function> specBuilder = specsBuilder[i++];
      LocBuilder locBuilder = specBuilder.initLoc();
      stubs::Decl::Function::Builder descBuilder = specBuilder.initDesc();
      m_ASTSerializer->serialize(locBuilder, spec->getSourceRange());
      serializeFunctionDecl(descBuilder, spec, false);
    }

    return true;
  }

  bool serialize(const clang::Decl *decl) {
    if (Visit(decl)) {
      return true;
    }

    clang::DiagnosticsEngine &diagsEngine =
        m_ASTSerializer->getASTContext().getDiagnostics();
    unsigned diagID = diagsEngine.getCustomDiagID(
        clang::DiagnosticsEngine::Error,
        "Declaration of kind '%0' is not supported");
    diagsEngine.Report(decl->getBeginLoc(), diagID) << decl->getDeclKindName();
    return false;
  }

  DeclSerializerImpl(const ASTSerializer &serializer,
                     stubs::Decl::Builder builder)
      : m_builder(builder), m_ASTSerializer(&serializer) {}

  stubs::Decl::Builder m_builder;
  const ASTSerializer *m_ASTSerializer;
};

} // namespace

void DeclSerializer::serialize(const clang::Decl *decl, LocBuilder locBuilder,
                               stubs::Decl::Builder declBuilder) const {
  assert(decl && "Decl should not be null");

  clang::SourceRange range = getRange(decl);
  DeclSerializerImpl serializer(*m_ASTSerializer, declBuilder);
  serializer.serialize(decl);
  m_ASTSerializer->serialize(locBuilder, range);
}

void DeclSerializer::serialize(const Annotation &annotation,
                               LocBuilder locBuilder,
                               stubs::Decl::Builder declBuilder) const {
  clang::SourceRange range = annotation.getRange();
  m_ASTSerializer->serialize(locBuilder, range);
  declBuilder.setAnn(annotation.getText().data());
}

} // namespace vf