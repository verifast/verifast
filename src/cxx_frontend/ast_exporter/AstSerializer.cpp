#include "AstSerializer.h"
#include "FixedWidthInt.h"
#include <list>

namespace vf {

void AstSerializer::updateFirstDeclLoc(unsigned fileUID,
                                       clang::SourceLocation newLoc) {
  if (m_firstDeclLocMap.find(fileUID) != m_firstDeclLocMap.end())
    return;

  m_firstDeclLocMap.emplace(fileUID, newLoc);
}

void AstSerializer::serializeDeclToDeclMap(const clang::Decl *decl,
                                           capnp::Orphanage &orphanage) {
  auto range = decl->getSourceRange();
  auto fileID = m_SM.getFileID(range.getBegin());
  auto fileUID = m_SM.getFileEntryForID(fileID)->getUID();
  auto &declNodeOrphans = m_fileDeclsMap[fileUID];

  std::list<Annotation> anns;
  m_store.getUntilLoc(anns, range.getBegin(), m_SM);
  serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);
  serializeToOrphan(decl, orphanage, declNodeOrphans);

  auto firstDeclLoc =
      !anns.empty() ? anns.front().getRange().getBegin() : range.getBegin();
  updateFirstDeclLoc(fileUID, firstDeclLoc);
}

void AstSerializer::serializeTU(stubs::TU::Builder &builder,
                                const clang::TranslationUnitDecl *tu) {
  auto orphanage = capnp::Orphanage::getForMessageContaining(builder);

  // Serialize every declaration in the translation unit.
  // Also serialize declaration annotations that appear before regular C++
  // declarations.
  clang::SourceLocation currentLoc;
  for (auto decl : tu->decls()) {
    auto range = decl->getSourceRange();
    if (range.isValid() && !decl->isImplicit()) {
      serializeDeclToDeclMap(decl, orphanage);
      currentLoc = range.getEnd();
    }
  }

  builder.setMainFd(m_SM.getFileEntryForID(m_SM.getMainFileID())->getUID());

  clang::SmallVector<const clang::FileEntry *, 4> fileEntries;
  m_SM.getFileManager().GetUniqueIDMapping(fileEntries);
  auto files = builder.initFiles(fileEntries.size());

  for (size_t i(0); i < fileEntries.size(); ++i) {
    auto fileEntry = fileEntries[i];
    auto fileUID = fileEntry->getUID();
    auto file = files[i];
    auto &declNodeOrphans = m_fileDeclsMap[fileUID];

    // Make sure to retrieve annotations after the last C++ declaration
    std::list<Annotation> anns;
    m_store.getAll(fileUID, anns);
    serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);

    file.setFd(fileUID);
    file.setPath(fileEntry->getName().str());

    auto fileDecls = file.initDecls(declNodeOrphans.size());
    adoptOrphansToListBuilder(declNodeOrphans, fileDecls);
  }

  std::function<llvm::Optional<clang::SourceLocation>(unsigned)>
      getFirstDeclOpt = [&map = m_firstDeclLocMap](unsigned fd) {
        auto it = map.find(fd);
        llvm::Optional<clang::SourceLocation> result;
        if (it != map.end()) {
          result.emplace(it->second);
        }
        return result;
      };

  c_inclContext.serializeTUInclDirectives(builder, m_SM, getFirstDeclOpt);
}

} // namespace vf