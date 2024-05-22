#include "TypeSerializer.h"
#include "Location.h"
#include "clang/AST/TypeLocVisitor.h"
#include "clang/AST/TypeVisitor.h"

namespace vf {

namespace {

struct TypeSerializerImpl
    : public clang::TypeVisitor<TypeSerializerImpl, bool> {

  bool VisitBuiltinType(const clang::BuiltinType *type) {
#define CASE_TYPE(CLANG_TYPE, STUBS_TYPE)                                      \
  case clang::BuiltinType::Kind::CLANG_TYPE:                                   \
    m_builder.setBuiltin(stubs::Type::BuiltinKind::STUBS_TYPE);                \
    return true;

#define CASE_TYPE_FW(CLANG_TYPE, STUBS_TYPE, BITS)                             \
  case clang::BuiltinType::Kind::CLANG_TYPE: {                                 \
    auto FWBuilder = m_builder.initFixedWidth();                               \
    FWBuilder.setKind(stubs::Type::FixedWidth::FixedWidthKind::STUBS_TYPE);    \
    FWBuilder.setBits(BITS);                                                   \
    return true;                                                               \
  }

    switch (type->getKind()) {
      CASE_TYPE(Char_U, CHAR)
      CASE_TYPE(Char_S, CHAR)
      CASE_TYPE(UChar, U_CHAR)
      CASE_TYPE(SChar, CHAR)
      CASE_TYPE(Void, VOID)
      CASE_TYPE(Int, INT)
      CASE_TYPE(UInt, U_INT)
      CASE_TYPE(Short, SHORT)
      CASE_TYPE(UShort, U_SHORT)
      CASE_TYPE(Long, LONG)
      CASE_TYPE(LongLong, LONG_LONG)
      CASE_TYPE(ULong, U_LONG)
      CASE_TYPE(ULongLong, U_LONG_LONG)
      CASE_TYPE(Bool, BOOL)
      CASE_TYPE_FW(Int128, INT, 128)
      CASE_TYPE_FW(UInt128, U_INT, 128)
    default:
      return false;
    }
#undef CASE_TYPE
#undef CASE_TYPE_FW
  }

  bool VisitPointerType(const clang::PointerType *type) {
    stubs::Type::Builder pointerBuilder = m_builder.initPointer().initDesc();
    m_ASTSerializer->serialize(pointerBuilder, type->getPointeeType());
    return true;
  }

  bool VisitRecordType(const clang::RecordType *type) {
    stubs::RecordRef::Builder recordBuilder = m_builder.initRecord();
    recordBuilder.setName(type->getDecl()->getQualifiedNameAsString());
    if (type->isClassType()) {
      recordBuilder.setKind(stubs::RecordKind::CLASS);
    } else if (type->isUnionType()) {
      recordBuilder.setKind(stubs::RecordKind::UNIO);
    } else if (type->isStructureType()) {
      recordBuilder.setKind(stubs::RecordKind::STRUC);
    } else {
      return false;
    }
    return true;
  }

  bool VisitEnumType(const clang::EnumType *type) {
    m_builder.setEnumType(type->getDecl()->getQualifiedNameAsString());
    return true;
  }

  bool VisitElaboratedType(const clang::ElaboratedType *type) {
    stubs::Type::Builder elaboratedBuilder =
        m_builder.initElaborated().initDesc();
    m_ASTSerializer->serialize(elaboratedBuilder, type->getNamedType());
    return true;
  }

  bool VisitTypedefType(const clang::TypedefType *type) {
    m_builder.setTypedef(type->getDecl()->getQualifiedNameAsString());
    return true;
  }

  bool VisitLValueReferenceType(const clang::LValueReferenceType *type) {
    stubs::Type::Builder refBuilder = m_builder.initLValueRef().initDesc();
    m_ASTSerializer->serialize(refBuilder, type->getPointeeType());
    return true;
  }

  bool VisitRValueReferenceType(const clang::RValueReferenceType *type) {
    stubs::Type::Builder refBuilder = m_builder.initRValueRef().initDesc();
    m_ASTSerializer->serialize(refBuilder, type->getPointeeType());
    return true;
  }

  bool
  VisitSubstTemplateTypeParmType(const clang::SubstTemplateTypeParmType *type) {
    stubs::Type::Builder substTemplateTypeParamBuilder =
        m_builder.initSubstTemplateTypeParam().initDesc();
    m_ASTSerializer->serialize(substTemplateTypeParamBuilder,
                               type->getReplacementType());
    return true;
  }

  bool serialize(const clang::Type *type) {
    if (Visit(type)) {
      return true;
    }

    clang::DiagnosticsEngine &diagsEngine =
        m_ASTSerializer->getASTContext().getDiagnostics();
    unsigned diagID = diagsEngine.getCustomDiagID(
        clang::DiagnosticsEngine::Error, "Type of kind '%0' is not supported");
    diagsEngine.Report(diagID) << type->getTypeClassName();

    return false;
  }

  TypeSerializerImpl(const ASTSerializer &serializer,
                     stubs::Type::Builder builder)
      : m_builder(builder), m_ASTSerializer(&serializer) {}

  stubs::Type::Builder m_builder;
  const ASTSerializer *m_ASTSerializer;
};

struct TypeLocSerializerImpl
    : public clang::TypeLocVisitor<TypeLocSerializerImpl, bool> {

  TypeLocSerializerImpl(const ASTSerializer &serializer,
                        stubs::Type::Builder builder)
      : m_builder(builder), m_ASTSerializer(&serializer) {}

  bool VisitFunctionProtoTypeLoc(const clang::FunctionProtoTypeLoc typeLoc) {
    stubs::Type::FunctionProto::Builder protoTypeBuilder =
        m_builder.initFunctionProto();
    TypeNodeBuilder returnTypeBuilder = protoTypeBuilder.initReturnType();
    m_ASTSerializer->serialize(returnTypeBuilder, typeLoc.getReturnLoc());

    AnnotationsRef ghostParams =
        m_ASTSerializer->getAnnotationManager().getInRange(
            typeLoc.getReturnLoc().getEndLoc(), typeLoc.getLParenLoc());
    m_ASTSerializer->serialize(
        protoTypeBuilder.initGhostParams(ghostParams.size()), ghostParams);

    ListBuilder<stubs::Param> paramsBuilder =
        protoTypeBuilder.initParams(typeLoc.getNumParams());
    m_ASTSerializer->serialize(paramsBuilder, typeLoc.getParams());

    AnnotationsRef contract =
        m_ASTSerializer->getAnnotationManager().getContract(typeLoc);
    ListBuilder<stubs::Clause> contractBuilder =
        protoTypeBuilder.initContract(contract.size());
    m_ASTSerializer->serialize(contractBuilder, contract);

    return true;
  }

  bool VisitPointerTypeLoc(const clang::PointerTypeLoc typeLoc) {
    TypeNodeBuilder pointerBuilder = m_builder.initPointer();
    m_ASTSerializer->serialize(pointerBuilder, typeLoc.getPointeeLoc());
    return true;
  }

  bool VisitElaboratedTypeLoc(const clang::ElaboratedTypeLoc typeLoc) {
    TypeNodeBuilder elaboratedBuilder = m_builder.initElaborated();
    m_ASTSerializer->serialize(elaboratedBuilder, typeLoc.getNamedTypeLoc());
    return true;
  }

  bool
  VisitLValueReferenceTypeLoc(const clang::LValueReferenceTypeLoc typeLoc) {
    TypeNodeBuilder refBuilder = m_builder.initLValueRef();
    m_ASTSerializer->serialize(refBuilder, typeLoc.getPointeeLoc());
    return true;
  }

  bool
  VisitRValueReferenceTypeLoc(const clang::RValueReferenceTypeLoc typeLoc) {
    TypeNodeBuilder refBuilder = m_builder.initRValueRef();
    m_ASTSerializer->serialize(refBuilder, typeLoc.getPointeeLoc());
    return true;
  }

  bool VisitSubstTemplateTypeParmType(
      const clang::SubstTemplateTypeParmTypeLoc typeLoc) {
    TypeNodeBuilder substTemplateTypeParamBuilder =
        m_builder.initSubstTemplateTypeParam();
    LocBuilder locBuilder = substTemplateTypeParamBuilder.initLoc();
    stubs::Type::Builder descBuilder = substTemplateTypeParamBuilder.initDesc();

    m_ASTSerializer->serialize(locBuilder, typeLoc.getSourceRange());
    m_ASTSerializer->serialize(descBuilder,
                               typeLoc.getTypePtr()->getReplacementType());
    return true;
  }

  bool serialize(clang::TypeLoc typeLoc) {
    if (Visit(typeLoc)) {
      return true;
    }

    // Try to delegate serialization to a serializer for types that do not have
    // a source range.
    TypeSerializerImpl delegateSerializer(*m_ASTSerializer, m_builder);
    if (delegateSerializer.serialize(typeLoc.getTypePtr())) {
      return true;
    }

    return false;
  }

  stubs::Type::Builder m_builder;
  const ASTSerializer *m_ASTSerializer;
};

} // namespace

void TypeSerializer::serialize(const clang::Type *type,
                               stubs::Type::Builder builder) const {
  assert(type && "Type should not be null");

  TypeSerializerImpl serializer(*m_ASTSerializer, builder);

  if (serializer.Visit(type)) {
    return;
  }

  clang::DiagnosticsEngine &diagsEngine =
      m_ASTSerializer->getASTContext().getDiagnostics();
  unsigned diagID = diagsEngine.getCustomDiagID(
      clang::DiagnosticsEngine::Error, "Type of kind '%0' is not supported");
  diagsEngine.Report(diagID) << type->getTypeClassName();
}

void TypeLocSerializer::serialize(clang::TypeLoc typeLoc, LocBuilder locBuilder,
                                  stubs::Type::Builder typeBuilder) const {
  assert(!typeLoc.isNull() && "TypeLoc should not be null");

  clang::SourceRange range = getRange(typeLoc);
  TypeLocSerializerImpl serializer(*m_ASTSerializer, typeBuilder);
  m_ASTSerializer->serialize(locBuilder, range);
  if (serializer.serialize(typeLoc)) {
    return;
  }

  clang::DiagnosticsEngine &diagsEngine =
      m_ASTSerializer->getASTContext().getDiagnostics();
  unsigned diagID = diagsEngine.getCustomDiagID(
      clang::DiagnosticsEngine::Error, "TypeLoc of kind '%0' is not supported");
  diagsEngine.Report(typeLoc.getSourceRange().getBegin(), diagID)
      << typeLoc.getTypePtr()->getTypeClassName();
}

} // namespace vf