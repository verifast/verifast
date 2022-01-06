#include "AstSerializer.h"
#include "clang/AST/Type.h"
#include <iostream>

namespace vf {

bool TypeSerializer::VisitBuiltinType(const clang::BuiltinType *type) {
#define CASE_TYPE(CLANG_TYPE, STUBS_TYPE)                                      \
  case clang::BuiltinType::Kind::CLANG_TYPE:                                   \
    _builder.setBuiltin(stubs::Type::BuiltinKind::STUBS_TYPE);                 \
    return true;

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
  default:
    return false;
  }
#undef CASE_TYPE
}

bool TypeSerializer::VisitPointerType(const clang::PointerType *type) {
  auto pointer = _builder.initPointer();
  getSerializer()->serializeType(pointer, type->getPointeeType().getTypePtr());
  return true;
}

// bool TypeSerializer::VisitFunctionProtoType(
//     const clang::FunctionProtoType *type) {
//   return Visit(type->getReturnType().getTypePtr());
// }

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

bool TypeSerializer::VisitElaboratedType(const clang::ElaboratedType *type) {
  return Visit(type->desugar().getTypePtr());
}

bool TypeSerializer::VisitTypedefType(const clang::TypedefType *type) {
  return Visit(type->desugar().getTypePtr());
}

bool TypeLocSerializer::VisitPointerTypeLoc(const clang::PointerTypeLoc type) {
  auto pointer = _builder.initPointerLoc();
  getSerializer()->serializeTypeLoc(pointer, type.getNextTypeLoc());
  return true;
}

void TypeSerializer::serializeReferenceType(stubs::Type::Builder &builder, const clang::ReferenceType *type) {
  getSerializer()->serializeType(builder, type->getPointeeType().getTypePtr());
}

bool TypeSerializer::VisitLValueReferenceType(const clang::LValueReferenceType *type) {
  auto ref = _builder.initLValueRef();
  serializeReferenceType(ref, type);
  return true;
}

bool TypeSerializer::VisitRValueReferenceType(const clang::RValueReferenceType *type) {
  auto ref = _builder.initRValueRef();
  serializeReferenceType(ref, type);
  return true;
}

} // namespace vf