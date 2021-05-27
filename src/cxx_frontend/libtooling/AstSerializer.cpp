#include "AstSerializer.h"
#include <list>

namespace vf {

void AstSerializer::serializeTU(stubs::TU::Builder &builder,
                                const clang::TranslationUnitDecl *tu) {
  using DeclNodeOrphan = AstSerializer::NodeOrphan<stubs::Decl>;
  auto orphanage = capnp::Orphanage::getForMessageContaining(builder);

  llvm::SmallVector<DeclNodeOrphan, 32> declNodeOrphans;

  // Serialize every declaration in the translation unit.
  // Also serialize declaration annotations that appear before regular C++
  // declarations.
  clang::SourceLocation currentLoc;
  for (auto decl : tu->decls()) {
    auto range = decl->getSourceRange();
    if (range.isValid() /* TODO: needed once we pass headers separately to verifast -> && _SM.isInMainFile(decl->getLocation()) */) {
      std::list<Annotation> anns;
      _store.getUntilLoc(anns, range.getBegin(), _SM);
      serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);
      serializeToOrphan(decl, orphanage, declNodeOrphans);
      currentLoc = range.getEnd();
    }
  }

  std::list<Annotation> anns;
  _store.getAll(currentLoc, anns, _SM);
  serializeAnnsToOrphans(anns, orphanage, declNodeOrphans);

  auto children = builder.initDecls(declNodeOrphans.size());
  adoptOrphansToListBuilder(declNodeOrphans, children);

  llvm::SmallVector<std::pair<unsigned, clang::StringRef>, 8> files;
  for (auto it = _SM.fileinfo_begin(); it != _SM.fileinfo_end(); ++it) {
    auto fileEntry = it->getFirst();
    files.emplace_back(fileEntry->getUID(), fileEntry->getName());
  }

  auto fileList = builder.initFiles(files.size());
  size_t i(0);
  for (const auto &entry : files) {
    auto file = fileList[i++];
    file.setFd(entry.first);
    file.setName(entry.second.str());
  }
}

} // namespace vf