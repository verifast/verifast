#include "AstSerializer.h"
#include "Util.h"
#include "clang/AST/Type.h"
#include "clang/AST/TypeLoc.h"

namespace vf {

// TypeSerializer

bool TypeSerializer::VisitBuiltinType(const clang::BuiltinType *type) {
#define CASE_TYPE(CLANG_TYPE, STUBS_TYPE)                                      \
  case clang::BuiltinType::Kind::CLANG_TYPE:                                   \
    m_builder.setBuiltin(stubs::Type::BuiltinKind::STUBS_TYPE);                \
    return true;

#define CASE_TYPE_FW(CLANG_TYPE, STUBS_TYPE, BITS)                             \
  case clang::BuiltinType::Kind::CLANG_TYPE: {                                 \
    auto fw = m_builder.initFixedWidth();                                      \
    fw.setKind(stubs::Type::FixedWidth::FixedWidthKind::STUBS_TYPE);           \
    fw.setBits(BITS);                                                          \
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

bool TypeSerializer::VisitPointerType(const clang::PointerType *type) {
  auto pointer = m_builder.initPointer().initDesc();
  m_serializer.serializeQualType(pointer, type->getPointeeType());
  return true;
}

bool TypeSerializer::VisitRecordType(const clang::RecordType *type) {
  auto rec = m_builder.initRecord();
  rec.setName(type->getDecl()->getQualifiedNameAsString());
  if (type->isClassType()) {
    rec.setKind(stubs::RecordKind::CLASS);
  } else if (type->isUnionType()) {
    rec.setKind(stubs::RecordKind::UNIO);
  } else if (type->isStructureType()) {
    rec.setKind(stubs::RecordKind::STRUC);
  } else {
    return false;
  }
  return true;
}

bool TypeSerializer::VisitEnumType(const clang::EnumType *type) {
  m_builder.setEnumType(type->getDecl()->getQualifiedNameAsString());
  return true;
}

bool TypeSerializer::VisitElaboratedType(const clang::ElaboratedType *type) {
  auto elaborated = m_builder.initElaborated().initDesc();
  m_serializer.serializeQualType(elaborated, type->getNamedType());
  return true;
}

bool TypeSerializer::VisitTypedefType(const clang::TypedefType *type) {
  m_builder.setTypedef(type->getDecl()->getQualifiedNameAsString());
  return true;
}

bool TypeSerializer::VisitLValueReferenceType(
    const clang::LValueReferenceType *type) {
  auto ref = m_builder.initLValueRef().initDesc();
  m_serializer.serializeQualType(ref, type->getPointeeType());
  return true;
}

bool TypeSerializer::VisitRValueReferenceType(
    const clang::RValueReferenceType *type) {
  auto ref = m_builder.initRValueRef().initDesc();
  m_serializer.serializeQualType(ref, type->getPointeeType());
  return true;
}

bool TypeLocSerializer::VisitFunctionProtoTypeLoc(
    const clang::FunctionProtoTypeLoc typeLoc) {
  auto proto = m_builder.initFunctionProto();
  auto ret = proto.initReturnType();

  m_serializer.serializeTypeLoc(ret, typeLoc.getReturnLoc());

  auto &store = m_serializer.getAnnStore();
  auto &SM = getSourceManager();
  llvm::SmallVector<Annotation> anns;

  store.getUntilLoc(anns, typeLoc.getLParenLoc(), SM);
  auto ghostParams = proto.initGhostParams(anns.size());
  m_serializer.serializeAnnotationClauses(ghostParams, anns);

  auto params = proto.initParams(typeLoc.getNumParams());
  m_serializer.serializeParams(params, typeLoc.getParams());

  anns.clear();

  store.guessContract(getFileEntry(typeLoc.getBeginLoc(), SM), anns, SM,
                    clang::SourceLocation());
  auto contract = proto.initContract(anns.size());
  m_serializer.serializeAnnotationClauses(contract, anns);

  return true;
}

bool TypeLocSerializer::VisitPointerTypeLoc(
    const clang::PointerTypeLoc typeLoc) {
  auto pointer = m_builder.initPointer();
  m_serializer.serializeTypeLoc(pointer, typeLoc.getPointeeLoc());
  return true;
}

bool TypeLocSerializer::VisitElaboratedTypeLoc(
    const clang::ElaboratedTypeLoc typeLoc) {
  auto elaborated = m_builder.initElaborated();
  m_serializer.serializeTypeLoc(elaborated, typeLoc.getNamedTypeLoc());
  return true;
}

bool TypeLocSerializer::VisitLValueReferenceTypeLoc(
    const clang::LValueReferenceTypeLoc typeLoc) {
  auto ref = m_builder.initLValueRef();
  m_serializer.serializeTypeLoc(ref, typeLoc.getPointeeLoc());
  return true;
}

bool TypeLocSerializer::VisitRValueReferenceTypeLoc(
    const clang::RValueReferenceTypeLoc typeLoc) {
  auto ref = m_builder.initRValueRef();
  m_serializer.serializeTypeLoc(ref, typeLoc.getPointeeLoc());
  return true;
}

}; // namespace vf