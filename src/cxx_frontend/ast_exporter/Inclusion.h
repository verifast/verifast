#pragma once
#include "Annotation.h"
#include "stubs_ast.capnp.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Lex/Preprocessor.h"
#include "llvm/ADT/SmallVector.h"

namespace vf {

struct IncludeDirective {
  IncludeDirective(clang::SourceRange range, std::string_view fileName,
                   unsigned fileUID, bool isAngled)
      : range(range), fileName(fileName), fileUID(fileUID), isAngled(isAngled) {
  }

  // #include "file" -> source range of "file"
  clang::SourceRange range;
  // file name as written in the source code
  std::string fileName;
  // actual file the include directive refers to
  unsigned fileUID;
  // angled or quoted
  bool isAngled;
};

class Inclusion {
public:
  void addIncludeDirective(IncludeDirective directive);

  void addInclusion(const Inclusion *inclusion);

  bool hasMacroDefinition(const clang::MacroDefinition &definition,
                          const clang::SourceManager &sourceManager) const;

  const clang::FileEntry *getFileEntry() const { return m_fileEntry; }

  llvm::ArrayRef<IncludeDirective> getIncludeDirectives() const;

  size_t nbIncludeDirectives() const;

  explicit Inclusion(const clang::FileEntry &fileEntry)
      : m_fileEntry(&fileEntry) {}

private:
  bool includesFile(const clang::FileEntry *fileEntry) const;

  llvm::SmallVector<const Inclusion *> m_inclusions;
  llvm::SmallVector<IncludeDirective> m_includeDirectives;

  const clang::FileEntry *m_fileEntry;
};

} // namespace vf