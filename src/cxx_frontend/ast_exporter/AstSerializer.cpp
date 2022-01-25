#include "AstSerializer.h"
#include <list>

namespace vf {

void AstSerializer::serializeDeclToDeclMap(const clang::Decl *decl,
                                           capnp::Orphanage &orphanage) {
  auto range = decl->getSourceRange();

  auto fileID = _SM.getFileID(range.getBegin());
  auto fileUID = _SM.getFileEntryForID(fileID)->getUID();
  auto &declNodeOrphans = _fileDeclsMap[fileUID];

  std::list<Annotation> anns;
  _store.getUntilLoc(anns, range.getBegin(), _SM);
  serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);
  serializeToOrphan(decl, orphanage, declNodeOrphans);

  if (_firstDeclLocMap.find(fileUID) == _firstDeclLocMap.end()) {
    auto firstDeclLoc =
        !anns.empty() ? anns.front().getRange().getBegin() : range.getBegin();
    _firstDeclLocMap.emplace(fileUID, firstDeclLoc);
  }
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
    if (range.isValid()) {
      serializeDeclToDeclMap(decl, orphanage);
      currentLoc = range.getEnd();
    }
  }

  builder.setMainFd(_SM.getFileEntryForID(_SM.getMainFileID())->getUID());

  clang::SmallVector<const clang::FileEntry *, 4> fileEntries;
  _SM.getFileManager().GetUniqueIDMapping(fileEntries);
  auto files = builder.initFiles(fileEntries.size());

  for (size_t i(0); i < fileEntries.size(); ++i) {
    auto fileEntry = fileEntries[i];
    auto fileUID = fileEntry->getUID();
    auto file = files[i];
    auto &declNodeOrphans = _fileDeclsMap[fileUID];

    // Make sure to retrieve annotations after the last C++ declaration
    std::list<Annotation> anns;
    _store.getAll(fileUID, anns);
    serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);

    file.setFd(fileUID);
    file.setPath(fileEntry->getName().str());

    auto fileDecls = file.initDecls(declNodeOrphans.size());
    adoptOrphansToListBuilder(declNodeOrphans, fileDecls);
  }

  std::function<llvm::Optional<clang::SourceLocation>(unsigned)>
      getFirstDeclOpt = [&map = _firstDeclLocMap](unsigned fd) {
        auto it = map.find(fd);
        llvm::Optional<clang::SourceLocation> result;
        if (it != map.end()) {
          result.emplace(it->second);
        }
        return result;
      };

  _inclContext.serializeTUInclDirectives(builder, _SM, getFirstDeclOpt);
}

} // namespace vf