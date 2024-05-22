#include "TranslationUnitSerializer.h"
#include "ASTSerializer.h"
#include "InclusionSerializer.h"
#include "Location.h"
#include "clang/Basic/FileManager.h"

namespace vf {

DeclListSerializer &
TranslationUnitSerializer::getDeclSerializer(unsigned uid) const {
  auto it = m_declsMap.find(uid);
  if (it != m_declsMap.end()) {
    return it->getSecond();
  }

  return m_declsMap.try_emplace(uid, m_orphanage, DeclSerializer(m_serializer))
      .first->getSecond();
}

namespace {

void updateFirstDecl(llvm::SmallDenseMap<unsigned, clang::SourceLocation> &map,
                     unsigned uid, clang::SourceLocation loc) {
  clang::SourceLocation foundLoc = map[uid];
  if (foundLoc.isInvalid() || loc < foundLoc) {
    map[uid] = loc;
  }
}

} // namespace

void TranslationUnitSerializer::serializeDecl(const clang::Decl *decl) const {
  clang::SourceRange declRange = decl->getSourceRange();

  const clang::FileEntry *fileEntry =
      fileEntryOfLoc(decl->getBeginLoc(), m_ASTContext->getSourceManager());
  unsigned fileUID = fileEntry->getUID();

  updateFirstDecl(m_firstDeclLocMap, fileUID, declRange.getBegin());
  DeclListSerializer &declSerializer = getDeclSerializer(fileUID);

  if (declSerializer.size() == 0) {
    AnnotationsRef leadingAnnotations =
        m_annotationManager->getInRange({}, declRange.getBegin());
    declSerializer << leadingAnnotations;
  }

  clang::Token nextToken(getNextToken(decl->getEndLoc(),
                                      m_ASTContext->getSourceManager(),
                                      m_ASTContext->getLangOpts()));
  declSerializer
      << decl
      << m_annotationManager
             ->getSequenceAfterLoc(nextToken.is(clang::tok::semi)
                                       ? nextToken.getLocation()
                                       : decl->getEndLoc())
             .drop_while(
                 Annotation::Predicate<Annotation::Ann_ContractClause>());
}

void TranslationUnitSerializer::serializeFile(
    const clang::FileEntry *fileEntry, stubs::File::Builder fileBuilder) const {
  DeclListSerializer &declSerializer = getDeclSerializer(fileEntry->getUID());

  if (declSerializer.size() == 0) {
    declSerializer << m_annotationManager->getAll(fileEntry);
  }

  fileBuilder.setFd(fileEntry->getUID());
  fileBuilder.setPath(fileEntry->getName().str());

  declSerializer.adoptToListBuilder(
      fileBuilder.initDecls(declSerializer.size()));
}

void TranslationUnitSerializer::serialize(
    const clang::TranslationUnitDecl *translationUnitDecl,
    stubs::TU::Builder translationUnitBuilder) const {
  for (const clang::Decl *decl : translationUnitDecl->decls()) {
    if (decl->getSourceRange().isInvalid() ||
        (decl->isImplicit() && m_serializer.skipImplicitDecls())) {
      continue;
    }
    serializeDecl(decl);
  }

  llvm::SmallVector<const clang::FileEntry *> fileEntries;
  m_ASTContext->getSourceManager().getFileManager().GetUniqueIDMapping(
      fileEntries);
  ListBuilder<stubs::File> filesBuilder =
      translationUnitBuilder.initFiles(fileEntries.size());

  size_t i(0);
  for (const clang::FileEntry *entry : fileEntries) {
    stubs::File::Builder fileBuilder = filesBuilder[i++];
    serializeFile(entry, fileBuilder);
  }

  clang::FileID mainUID = m_ASTContext->getSourceManager().getMainFileID();
  const clang::FileEntry *mainEntry =
      m_ASTContext->getSourceManager().getFileEntryForID(mainUID);
  translationUnitBuilder.setMainFd(mainEntry->getUID());

  llvm::ArrayRef<Text> failDirectives =
      m_annotationManager->getFailDirectives();
  ListBuilder<stubs::Clause> failDirectivesBuilder =
      translationUnitBuilder.initFailDirectives(failDirectives.size());
  m_serializer.serialize(failDirectivesBuilder, failDirectives);

  const Inclusion &mainInclusion =
      m_inclusionContext->getInclusionOfFileUID(mainEntry->getUID());
  size_t nbIncludes = mainInclusion.nbIncludeDirectives() +
                      m_annotationManager->getLeadingIncludes(mainEntry).size();
  InclusionSerializer inclusionSerializer(m_serializer, *m_inclusionContext,
                                          m_firstDeclLocMap);
  inclusionSerializer.serialize(
      mainInclusion, translationUnitBuilder.initIncludes(nbIncludes));
}

} // namespace vf