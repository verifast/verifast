#include "AstSerializer.h"
#include "clang/AST/Type.h"
#include "clang/AST/TypeLoc.h"

namespace vf {

// TypeSerializer

bool TypeSerializer::VisitBuiltinType(const clang::BuiltinType *type) {
#define CASE_TYPE(CLANG_TYPE, STUBS_TYPE)                                      \
  case clang::BuiltinType::Kind::CLANG_TYPE:                                   \
    _builder.setBuiltin(stubs::Type::BuiltinKind::STUBS_TYPE);                 \
    return true;

#define CASE_TYPE_FW(CLANG_TYPE, STUBS_TYPE, BITS)                             \
  case clang::BuiltinType::Kind::CLANG_TYPE: {                                 \
    auto fw = _builder.initFixedWidth();                                        \
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
  auto pointer = _builder.initPointer().initDesc();
  _serializer.serializeQualType(pointer, type->getPointeeType());
  return true;
}

bool TypeSerializer::VisitRecordType(const clang::RecordType *type) {
  auto rec = _builder.initRecord();
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
  _builder.setEnumType(type->getDecl()->getQualifiedNameAsString());
  return true;
}

bool TypeSerializer::VisitElaboratedType(
    const clang::ElaboratedType *type) {
  auto elaborated = _builder.initElaborated().initDesc();
  _serializer.serializeQualType(elaborated, type->getNamedType());
  return true;
}

bool TypeSerializer::VisitTypedefType(const clang::TypedefType *type) {
  _builder.setTypedef(type->getDecl()->getQualifiedNameAsString());
  return true;
}

bool TypeSerializer::VisitLValueReferenceType(
    const clang::LValueReferenceType *type) {
  auto ref = _builder.initLValueRef().initDesc();
  _serializer.serializeQualType(ref, type->getPointeeType());
  return true;
}

bool TypeSerializer::VisitRValueReferenceType(
    const clang::RValueReferenceType *type) {
  auto ref = _builder.initRValueRef().initDesc();
  _serializer.serializeQualType(ref, type->getPointeeType());
  return true;
}

bool TypeLocSerializer::VisitPointerTypeLoc(const clang::PointerTypeLoc typeLoc) {
  auto pointer = _builder.initPointer();
  _serializer.serializeTypeLoc(pointer, typeLoc.getPointeeLoc());
  return true;
}

bool TypeLocSerializer::VisitElaboratedTypeLoc(
    const clang::ElaboratedTypeLoc typeLoc) {
  auto elaborated = _builder.initElaborated();
  _serializer.serializeTypeLoc(elaborated, typeLoc.getNamedTypeLoc());
  return true;
}

bool TypeLocSerializer::VisitLValueReferenceTypeLoc(
    const clang::LValueReferenceTypeLoc typeLoc) {
  auto ref = _builder.initLValueRef();
  _serializer.serializeTypeLoc(ref, typeLoc.getPointeeLoc());
  return true;
}

bool TypeLocSerializer::VisitRValueReferenceTypeLoc(
    const clang::RValueReferenceTypeLoc typeLoc) {
  auto ref = _builder.initRValueRef();
  _serializer.serializeTypeLoc(ref, typeLoc.getPointeeLoc());
  return true;
}

}; // namespace vf