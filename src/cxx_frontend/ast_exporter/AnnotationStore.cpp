#include "AnnotationStore.h"
#include "Util.h"
#include "clang/AST/Stmt.h"

namespace vf {

void AnnotationStore::add(Annotation &&ann, const clang::SourceManager &SM) {
  auto entry = getFileEntry(ann.getRange().getBegin(), SM);
  getCont(entry).add(std::move(ann));
}

void AnnotationStore::AnnCont::getWhile(
    llvm::SmallVectorImpl<Annotation> &container, AnnotationPred pred) {
  while (m_pos < m_anns.size()) {
    auto ann = m_anns.at(m_pos);
    if (pred(ann)) {
      container.push_back(ann);
      ++m_pos;
      continue;
    }
    return;
  }
}

void AnnotationStore::AnnCont::getAll(
    llvm::SmallVectorImpl<Annotation> &container) {
  while (m_pos < m_anns.size()) {
    container.push_back(m_anns.at(m_pos++));
  }
}

void AnnotationStore::getUntilLoc(llvm::SmallVectorImpl<Annotation> &container,
                                  clang::SourceLocation loc,
                                  const clang::SourceManager &SM) {
  auto expLoc = SM.getExpansionLoc(loc);
  auto pred = [expLoc](const Annotation &ann) {
    // compare to 'begin' of range in case the end overlaps with the given loc
    return ann.getRange().getBegin() < expLoc;
  };
  getCont(getFileEntry(expLoc, SM)).getWhile(container, pred);
}

void AnnotationStore::getAll(const clang::FileEntry *entry,
                             llvm::SmallVectorImpl<Annotation> &container) {
  getCont(entry).getAll(container);
}

const clang::Decl *findNextExplicitDeclInContext(const clang::Decl *decl) {
  const auto *nextDecl = decl->getNextDeclInContext();
  while (nextDecl && nextDecl->isImplicit()) {
    nextDecl = nextDecl->getNextDeclInContext();
  }
  return nextDecl;
}

void AnnotationStore::guessContract(
    const clang::FileEntry *entry, llvm::SmallVectorImpl<Annotation> &container,
    const clang::SourceManager &SM, clang::SourceLocation maxEndLoc) {
  auto expLoc = SM.getExpansionLoc(maxEndLoc);
  bool first = true;
  auto pred = [&first, expLoc](const Annotation &ann) {
    bool beforeLoc =
        expLoc.isValid() ? ann.getRange().getBegin() < expLoc : true;
    bool result =
        beforeLoc && ann.isContractClauseLike() && first == ann.isNewSeq();
    first = false;
    return result;
  };
  // Do best guess
  getCont(entry).getWhile(container, pred);
}

void AnnotationStore::getContract(const clang::FileEntry *entry,
                                  llvm::SmallVectorImpl<Annotation> &container,
                                  const clang::SourceManager &SM,
                                  clang::SourceLocation bodyStartLoc) {
  if (bodyStartLoc.isValid()) {
    return getUntilLoc(container, bodyStartLoc, SM);
  }
  guessContract(entry, container, SM, bodyStartLoc);
}

void AnnotationStore::getContract(const clang::FunctionDecl *decl,
                                  llvm::SmallVectorImpl<Annotation> &container,
                                  const clang::SourceManager &SM) {
  if (decl->isImplicit())
    return;

  auto startLoc = decl->getBeginLoc();
  auto *entry = getFileEntry(startLoc, SM);

  if (decl->isThisDeclarationADefinition()) {
    getContract(entry, container, SM, decl->getBody()->getBeginLoc());
    return;
  }

  const auto *nextDecl = findNextExplicitDeclInContext(decl);

  if (nextDecl) {
    guessContract(entry, container, SM, nextDecl->getBeginLoc());
    return;
  }

  guessContract(entry, container, SM,
                nextDecl ? nextDecl->getBeginLoc() : clang::SourceLocation());
}

llvm::Optional<clang::SourceRange> AnnotationStore::queryTruncatingAnnotation(
    const clang::SourceLocation currentLoc, const clang::SourceManager &SM) {
  auto pred = [&currentLoc](const Annotation &ann) {
    // compare to 'begin' of range in case the end overlaps with the given
    // currentLoc
    return ann.getRange().getBegin() < currentLoc && ann.isTruncating();
  };
  llvm::SmallVector<Annotation, 1> query;
  getCont(getFileEntry(currentLoc, SM)).getWhile(query, pred);
  llvm::Optional<clang::SourceRange> result;
  if (query.empty()) {
    return result;
  }
  result.emplace(query.front().getRange());
  return result;
}

void AnnotationStore::getGhostIncludeSequence(
    const clang::FileEntry *entry, llvm::SmallVectorImpl<Annotation> &container,
    const clang::SourceManager &SM) {
  auto pred = [](const Annotation &ann) { return ann.isInclude(); };
  getCont(entry).getWhile(container, pred);
}

} // namespace vf