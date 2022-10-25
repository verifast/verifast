#pragma once

#include "clang/Basic/FileManager.h"
#include "clang/Lex/Preprocessor.h"
#include "llvm/ADT/SmallVector.h"

namespace vf {

struct InclDirective {
  // #include "file" -> source range of "file"
  clang::SourceRange m_range;
  // file name as written in the source code
  clang::StringRef m_fileName;
  // actual file the include directive refers to
  unsigned m_fileUID;
  // angled or quoted
  bool m_isAngled;

  explicit InclDirective(clang::SourceRange range, clang::StringRef fileName,
                         unsigned fileUID, bool isAngled)
      : m_range(range), m_fileName(fileName), m_fileUID(fileUID),
        m_isAngled(isAngled) {}
};

class Inclusion {
  llvm::SmallVector<Inclusion *, 4> m_inclusions;
  llvm::SmallVector<InclDirective, 4> m_inclDirectives;

  bool containsInclusionFile(const clang::FileEntry &fileEntry) const {
    if (fileUID == fileEntry.getUID()) {
      return true;
    }
    for (auto incl : m_inclusions) {
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
    return m_inclDirectives;
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
    m_inclusions.emplace_back(inclusion);
  }

  void addInclDirective(clang::SourceRange range, clang::StringRef fileName,
                        unsigned fileUID, bool isAngled) {
    m_inclDirectives.emplace_back(range, fileName, fileUID, isAngled);
  }
};
} // namespace vf