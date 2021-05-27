#pragma once

#include "clang/Basic/FileManager.h"
#include "clang/Lex/Preprocessor.h"
#include "llvm/ADT/iterator_range.h"
#include <unordered_set>

namespace vf {
class Inclusion {
  std::unordered_set<Inclusion *> _inclusions;

  bool containsInclusionFile(const clang::FileEntry &fileEntry) const {
    if (fileUID == fileEntry.getUID()) {
      return true;
    }
    for (auto incl : _inclusions) {
      if (incl->containsInclusionFile(fileEntry)) {
        return true;
      }
    }
    return false;
  }

public:
  const unsigned fileUID;
  const llvm::StringRef fileName;
  explicit Inclusion(const clang::FileEntry &fileEntry)
      : fileUID(fileEntry.getUID()), fileName(fileEntry.getName()){};

  bool ownsMacroDef(const clang::MacroDefinition &macroDef,
                    const clang::SourceManager &SM) const {
    // macro info is null when no definition exists
    if (auto *macroInfo = macroDef.getMacroInfo()) {
      auto macroDefLoc = macroInfo->getDefinitionLoc();
      auto macroFileID = SM.getFileID(macroDefLoc);
      if (auto *macroFileEntry = SM.getFileEntryForID(macroFileID)) {
        return containsInclusionFile(*macroFileEntry);
      }
    }
    return false;
  }

  void addInclusion(Inclusion *inclusion) {
    // No cycles
    assert(this != inclusion);
    _inclusions.emplace(inclusion);
  }
};
} // namespace vf