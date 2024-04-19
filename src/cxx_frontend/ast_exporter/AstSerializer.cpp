#include "AstSerializer.h"
#include "FixedWidthInt.h"
#include "clang/AST/Decl.h"

namespace vf {

DeclListSerializer &AstSerializer::getDeclListSerializer(unsigned fd) {
  auto it = m_fileDeclsMap.find(fd);
  if (it != m_fileDeclsMap.end()) {
    return *it->second;
  }

  return *m_fileDeclsMap
              .emplace(fd,
                       std::make_unique<DeclListSerializer>(m_orphanage, *this))
              .first->second;
}

void AstSerializer::serializeDecl(DeclSerializer::NodeBuilder builder,
                                  const clang::Decl *decl) {
  DeclSerializer ser(m_ASTContext, *this, builder);
  ser.serialize(decl);
}

void AstSerializer::serializeStmt(StmtSerializer::NodeBuilder builder,
                                  const clang::Stmt *stmt) {
  StmtSerializer ser(m_ASTContext, *this, builder);
  ser.serialize(stmt);
}

void AstSerializer::serializeExpr(ExprSerializer::NodeBuilder builder,
                                  const clang::Expr *expr) {
  auto truncatingOptional =
      m_store.queryTruncatingAnnotation(expr->getBeginLoc(), m_SM);
  if (truncatingOptional) {
    auto loc = builder.initLoc();
    auto desc = builder.initDesc();

    serializeSourceRange(loc,
                         {truncatingOptional->getBegin(), expr->getEndLoc()},
                         m_SM, m_ASTContext.getLangOpts());
    auto truncating = desc.initTruncating();

    ExprSerializer ser(m_ASTContext, *this, truncating);
    ser.serialize(expr);
    return;
  }
  ExprSerializer ser(m_ASTContext, *this, builder);
  ser.serialize(expr);
}

void AstSerializer::serializeTypeLoc(TypeLocSerializer::NodeBuilder builder,
                                     const clang::TypeLoc typeLoc) {
  TypeLocSerializer ser(m_ASTContext, *this, builder);
  ser.serialize(typeLoc);
}

void AstSerializer::serializeQualType(TypeSerializer::DescBuilder builder,
                                      const clang::QualType type) {
  TypeSerializer ser(m_ASTContext, *this, builder);
  ser.serialize(type.getTypePtr());
}

void AstSerializer::serializeParams(
    capnp::List<stubs::Param, capnp::Kind::STRUCT>::Builder builder,
    llvm::ArrayRef<clang::ParmVarDecl *> params) {
  size_t i(0);
  for (auto p : params) {
    auto param = builder[i++];

    auto declName = p->getDeclName();
    param.setName(declName.getAsString());
    auto type = param.initType();
    auto typeInfo = p->getTypeSourceInfo();

    if (typeInfo) {
      serializeTypeLoc(type, typeInfo->getTypeLoc());
    } else {
      auto typeDesc = type.initDesc();
      serializeQualType(typeDesc, p->getType());
    }

    if (p->hasDefaultArg()) {
      auto def = param.initDefault();
      serializeExpr(def, p->getDefaultArg());
    }
  }
}

void AstSerializer::serializeAnnotationClauses(
    capnp::List<stubs::Clause, capnp::Kind::STRUCT>::Builder builder,
    const clang::ArrayRef<Annotation> anns) {
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
  auto &diagsEngine = getDiagsEngine();
  auto id = diagsEngine.getCustomDiagID(
      clang::DiagnosticsEngine::Error,
      "'#include' directive cannot appear after a declaration");
  diagsEngine.Report(lastDirective.getRange().getBegin(), id);
}

void AstSerializer::serializeDeclToDeclMap(const clang::Decl *decl,
                                           capnp::Orphanage &orphanage) {
  auto range = decl->getSourceRange();
  auto entry = getFileEntry(range.getBegin(), m_SM);
  auto fileUID = entry->getUID();
  DeclListSerializer &declListSerializer = getDeclListSerializer(fileUID);

  llvm::SmallVector<Annotation> anns;
  m_store.getUntilLoc(anns, range.getBegin(), m_SM);
  declListSerializer << anns << decl;
  auto firstDeclLoc =
      anns.empty() ? decl->getBeginLoc() : anns.front().getRange().getBegin();
  updateFirstDeclLoc(fileUID, firstDeclLoc);
}

void AstSerializer::serializeTU(stubs::TU::Builder builder,
                                const clang::TranslationUnitDecl *tu) {
  auto orphanage = capnp::Orphanage::getForMessageContaining(builder);

  clang::SmallVector<const clang::FileEntry *> fileEntries;
  m_SM.getFileManager().GetUniqueIDMapping(fileEntries);
  auto files = builder.initFiles(fileEntries.size());
  llvm::SmallVector<Annotation> anns;

  // Serialize ghost includes at start of file
  for (size_t i(0); i < fileEntries.size(); ++i) {
    auto fileEntry = fileEntries[i];
    if (fileEntry) {
      anns.clear();
      m_store.getGhostIncludeSequence(fileEntry, anns);
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
    DeclListSerializer &declListSerializer = getDeclListSerializer(fileUID);

    // Make sure to retrieve annotations after the last C++ declaration
    anns.clear();
    m_store.getAll(fileEntry, anns);
    declListSerializer << anns;

    file.setFd(fileUID);
    file.setPath(fileEntry->getName().str());

    auto fileDecls = file.initDecls(declListSerializer.size());
    declListSerializer.adoptListToBuilder(fileDecls);
  }

  m_inclContext.serializeTUInclDirectives(builder, m_SM, *this);

  auto failDirectives = m_store.getFailDirectives();
  auto failDirectivesBuilder =
      builder.initFailDirectives(failDirectives.size());
  size_t i(0);
  for (auto &directive : failDirectives) {
    auto directiveBuilder = failDirectivesBuilder[i++];
    m_textSerializer.serializeClause(directiveBuilder, directive);
  }
}

void AstSerializer::printQualifiedName(const clang::NamedDecl *decl,
                                       llvm::raw_string_ostream &os) const {
  decl->printQualifiedName(os, m_ASTContext.getPrintingPolicy());
}

std::string
AstSerializer::getQualifiedName(const clang::NamedDecl *decl) const {
  std::string s;
  llvm::raw_string_ostream os(s);
  printQualifiedName(decl, os);
  os.flush();
  return s;
}

std::string
AstSerializer::getQualifiedFuncName(const clang::FunctionDecl *decl) const {
  std::string s;
  llvm::raw_string_ostream os(s);
  printQualifiedName(decl, os);
  os << "(";
  auto *param = decl->param_begin();
  while (param != decl->param_end()) {
    (*param)->getOriginalType().print(os, m_ASTContext.getPrintingPolicy());
    ++param;
    if (param != decl->param_end()) {
      os << ", ";
    }
  }
  os << ")";
  os.flush();
  return s;
}

} // namespace vf