#pragma once

#include "clang/Basic/FileManager.h"
#include "clang/Lex/Preprocessor.h"
#include "llvm/ADT/SmallVector.h"

namespace vf {

struct InclDirective {
  // #include "file" -> source range of "file"
  clang::SourceRange _range;
  // file name as written in the source code
  clang::StringRef _fileName;
  // actual file the include directive refers to
  unsigned _fileUID;
  // angled or quoted
  bool _isAngled;

  explicit InclDirective(clang::SourceRange range, clang::StringRef fileName,
                unsigned fileUID, bool isAngled)
      : _range(range), _fileName(fileName), _fileUID(fileUID), _isAngled(isAngled) {}
};

class Inclusion {
  llvm::SmallVector<Inclusion *, 4> _inclusions;
  llvm::SmallVector<InclDirective, 4> _inclDirectives;

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

  const llvm::ArrayRef<InclDirective> getInclDirectives() const {
    return _inclDirectives;
  }

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
    _inclusions.emplace_back(inclusion);
  }

  void addInclDirective(clang::SourceRange range, clang::StringRef fileName,
                        unsigned fileUID, bool isAngled) {
    _inclDirectives.emplace_back(range, fileName, fileUID, isAngled);
  }
};
} // namespace vf