#include "AstSerializer.h"
#include "FixedWidthInt.h"
#include "clang/AST/Decl.h"

namespace vf {

void AstSerializer::serializeDecl(DeclSerializer::NodeBuilder &builder,
                                  const clang::Decl *decl) {
  if (!m_serializeImplicitDecls && decl->isImplicit())
    return;
  DeclSerializer ser(m_context, *this, builder, m_serializeImplicitDecls);
  ser.serialize(decl);
}

void AstSerializer::serializeStmt(StmtSerializer::NodeBuilder &builder,
                                  const clang::Stmt *stmt) {
  StmtSerializer ser(m_context, *this, builder);
  ser.serialize(stmt);
}

void AstSerializer::serializeExpr(ExprSerializer::NodeBuilder &builder,
                                  const clang::Expr *expr) {
  auto truncatingOptional =
      m_store.queryTruncatingAnnotation(expr->getBeginLoc(), m_SM);
  if (truncatingOptional) {
    auto loc = builder.initLoc();
    auto desc = builder.initDesc();

    serializeSrcRange(loc, {truncatingOptional->getBegin(), expr->getEndLoc()},
                      m_SM);
    auto truncating = desc.initTruncating();

    ExprSerializer ser(m_context, *this, truncating);
    ser.serialize(expr);
    return;
  }
  ExprSerializer ser(m_context, *this, builder);
  ser.serialize(expr);
}

void AstSerializer::serializeTypeLoc(TypeLocSerializer::NodeBuilder &builder,
                                     const clang::TypeLoc typeLoc) {
  TypeLocSerializer ser(m_context, *this, builder);
  ser.serialize(typeLoc);
}

void AstSerializer::serializeQualType(TypeSerializer::DescBuilder &builder,
                                      const clang::QualType type) {
  TypeSerializer ser(m_context, *this, builder);
  ser.serialize(type.getTypePtr());
}

void AstSerializer::serializeParams(
    capnp::List<stubs::Param, capnp::Kind::STRUCT>::Builder &builder,
    llvm::ArrayRef<clang::ParmVarDecl *> params) {
  size_t i(0);
  for (auto p : params) {
    auto param = builder[i++];

    auto declName = p->getDeclName();
    param.setName(declName.getAsString());
    auto type = param.initType();
    auto typeInfo = p->getTypeSourceInfo();

    assert(typeInfo && "Explicit parameter source info.");

    serializeTypeLoc(type, typeInfo->getTypeLoc());
    if (p->hasDefaultArg()) {
      auto def = param.initDefault();
      serializeExpr(def, p->getDefaultArg());
    }
  }
}

void AstSerializer::serializeNodeDecomposed(stubs::Loc::Builder &locBuilder,
                                            stubs::Decl::Builder &builder,
                                            const clang::Decl *decl) {
  if (!m_serializeImplicitDecls && decl->isImplicit())
    return;
  DeclSerializer ser(m_context, *this, locBuilder, builder,
                     m_serializeImplicitDecls);
  ser.serialize(decl);
}

void AstSerializer::serializeNodeDecomposed(stubs::Loc::Builder &locBuilder,
                                            stubs::Stmt::Builder &builder,
                                            const clang::Stmt *stmt) {
  StmtSerializer ser(m_context, *this, locBuilder, builder);
  ser.serialize(stmt);
}

void AstSerializer::serializeAnnotationClauses(
    capnp::List<stubs::Clause, capnp::Kind::STRUCT>::Builder &builder,
    clang::ArrayRef<Annotation> anns) {
  size_t i(0);
  for (auto &ann : anns) {
    auto annBuilder = builder[i++];
    serializeAnnotationClause(annBuilder, ann);
  }
}

void AstSerializer::updateFirstDeclLoc(unsigned fd, clang::SourceLocation loc) {
  if (m_firstDeclLocMap.find(fd) != m_firstDeclLocMap.end()) {
    return;
  }
  m_firstDeclLocMap.emplace(fd, loc);
}

llvm::Optional<clang::SourceLocation>
AstSerializer::getFirstDeclLocOpt(unsigned fd) const {
  llvm::Optional<clang::SourceLocation> result;
  auto it = m_firstDeclLocMap.find(fd);
  if (it != m_firstDeclLocMap.end()) {
    result.emplace(it->second);
  }
  return result;
}

void AstSerializer::validateIncludesBeforeFirstDecl(
    unsigned fd, clang::ArrayRef<std::reference_wrapper<const IncludeDirective>>
                     orderedDirectives) const {
  if (orderedDirectives.empty()) {
    return;
  }
  auto firstDeclLocOpt = getFirstDeclLocOpt(fd);
  if (!firstDeclLocOpt) {
    return;
  }
  const IncludeDirective &lastDirective = orderedDirectives.back();
  if (*firstDeclLocOpt > lastDirective.getRange().getEnd()) {
    return;
  }
  auto diagID = m_SM.getDiagnostics().getCustomDiagID(
      clang::DiagnosticsEngine::Level::Error,
      "An include directive cannot appear after a declaration.");
  m_SM.getDiagnostics().Report(lastDirective.getRange().getBegin(), diagID);
}

void AstSerializer::serializeDeclToDeclMap(const clang::Decl *decl,
                                           capnp::Orphanage &orphanage) {
  auto range = decl->getSourceRange();
  auto fileID = m_SM.getFileID(range.getBegin());
  auto fileUID = m_SM.getFileEntryForID(fileID)->getUID();
  auto &declNodeOrphans = m_fileDeclsMap[fileUID];

  llvm::SmallVector<Annotation> anns;
  m_store.getUntilLoc(anns, range.getBegin(), m_SM);
  serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);
  serializeToOrphan(decl, orphanage, declNodeOrphans);
  auto firstDeclLoc =
      anns.empty() ? decl->getBeginLoc() : anns.front().getRange().getBegin();
  updateFirstDeclLoc(fileUID, firstDeclLoc);
}

void AstSerializer::serializeTU(stubs::TU::Builder &builder,
                                const clang::TranslationUnitDecl *tu) {
  auto orphanage = capnp::Orphanage::getForMessageContaining(builder);

  clang::SmallVector<const clang::FileEntry *, 4> fileEntries;
  m_SM.getFileManager().GetUniqueIDMapping(fileEntries);
  auto files = builder.initFiles(fileEntries.size());
  llvm::SmallVector<Annotation> anns;

  // Serialize ghost includes at start of file
  for (size_t i(0); i < fileEntries.size(); ++i) {
    auto fileEntry = fileEntries[i];
    if (fileEntry && fileEntry->isValid()) {
      anns.clear();
      m_store.getGhostIncludeSequence(fileEntry, anns, m_SM);
      for (auto &ann : anns) {
        m_inclContext.addGhostInclDirective(fileEntry, ann);
      }
    }
  }

  // Serialize every declaration in the translation unit.
  for (auto decl : tu->decls()) {
    auto range = decl->getSourceRange();
    if (range.isValid() && (!decl->isImplicit() || m_serializeImplicitDecls)) {
      serializeDeclToDeclMap(decl, orphanage);
    }
  }

  builder.setMainFd(m_SM.getFileEntryForID(m_SM.getMainFileID())->getUID());

  for (size_t i(0); i < fileEntries.size(); ++i) {
    auto fileEntry = fileEntries[i];
    auto fileUID = fileEntry->getUID();
    auto file = files[i];
    auto &declNodeOrphans = m_fileDeclsMap[fileUID];

    // Make sure to retrieve annotations after the last C++ declaration
    anns.clear();
    m_store.getAll(fileEntry, anns);
    serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);

    file.setFd(fileUID);
    file.setPath(fileEntry->getName().str());

    auto fileDecls = file.initDecls(declNodeOrphans.size());
    adoptOrphansToListBuilder(declNodeOrphans, fileDecls);
  }

  m_inclContext.serializeTUInclDirectives(builder, m_SM, *this);
}

} // namespace vf