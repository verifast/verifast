#pragma once

#include "Annotation.h"
#include "stubs_ast.capnp.h"
#include "clang/Basic/FileManager.h"
#include "clang/Lex/Preprocessor.h"
#include "llvm/ADT/SmallVector.h"
#include <unordered_map>

namespace vf {

class InclusionContext;
class AstSerializer;

class IncludeDirective {
public:
  virtual ~IncludeDirective() {}

  virtual clang::SourceRange getRange() const = 0;

  virtual void serialize(stubs::Include::Builder &builder,
                         const clang::SourceManager &SM,
                         AstSerializer &serializer,
                         const InclusionContext &context) const = 0;
};

class RealIncludeDirective : public IncludeDirective {

  // #include "file" -> source range of "file"
  clang::SourceRange m_range;
  // file name as written in the source code
  clang::StringRef m_fileName;
  // actual file the include directive refers to
  unsigned m_fileUID;
  // angled or quoted
  bool m_isAngled;

public:
  explicit RealIncludeDirective(clang::SourceRange range,
                                clang::StringRef fileName, unsigned fileUID,
                                bool isAngled)
      : m_range(range), m_fileName(fileName), m_fileUID(fileUID),
        m_isAngled(isAngled) {}

  ~RealIncludeDirective() {}

  clang::SourceRange getRange() const override { return m_range; }

  void serialize(stubs::Include::Builder &builder,
                 const clang::SourceManager &SM, AstSerializer &serializer,
                 const InclusionContext &context) const override;
};

class GhostIncludeDirective : public IncludeDirective, public Annotation {
public:
  using Annotation::Annotation;

  ~GhostIncludeDirective() {}

  explicit GhostIncludeDirective(const Annotation &annotation)
      : Annotation(annotation) {}

  clang::SourceRange getRange() const override {
    return Annotation::getRange();
  }

  void serialize(stubs::Include::Builder &builder,
                 const clang::SourceManager &SM, AstSerializer &serializer,
                 const InclusionContext &context) const override;
};

class Inclusion {
  llvm::SmallVector<Inclusion *> m_inclusions;
  llvm::SmallVector<std::unique_ptr<IncludeDirective>> m_inclDirectives;

  bool containsInclusionFile(const clang::FileEntry &fileEntry) const;

public:
  unsigned m_fileUID;
  llvm::StringRef m_fileName;
  explicit Inclusion(const clang::FileEntry &fileEntry)
      : m_fileUID(fileEntry.getUID()), m_fileName(fileEntry.getName()){};

  unsigned getUID() const { return m_fileUID; }

  const llvm::StringRef getFileName() const { return m_fileName; }

  unsigned getNbIncludeDirectives() const { return m_inclDirectives.size(); }

  void sortIncludeDirectivesTo(
      std::vector<std::reference_wrapper<const IncludeDirective>> &container)
      const;

  bool ownsMacroDef(const clang::MacroDefinition &macroDef,
                    const clang::SourceManager &SM) const;

  void addInclusion(Inclusion *inclusion) {
    // No cycles
    assert(this != inclusion);
    m_inclusions.push_back(inclusion);
  }

  void addRealInclDirective(clang::SourceRange range, clang::StringRef fileName,
                            unsigned fileUID, bool isAngled) {
    m_inclDirectives.push_back(std::move(std::make_unique<RealIncludeDirective>(
        range, fileName, fileUID, isAngled)));
  }

  void addGhostInclDirective(Annotation &ann) {
    m_inclDirectives.push_back(
        std::move(std::make_unique<GhostIncludeDirective>(ann)));
  }

  void serializeIncludeDirectives(
      capnp::List<stubs::Include, capnp::Kind::STRUCT>::Builder &builder,
      const clang::SourceManager &SM, AstSerializer &serializer,
      const InclusionContext &context) const;
};

class InclusionContext {
  std::unordered_map<unsigned, Inclusion> m_includesMap;
  llvm::SmallVector<Inclusion *> m_includesStack;

  friend class ContextFreePPCallbacks;
  Inclusion *currentInclusion() {
    assert(hasInclusions() && "Empty stack of inclusions");
    return m_includesStack.back();
  }

public:
  explicit InclusionContext() {}

  KJ_DISALLOW_COPY(InclusionContext);

  const Inclusion &getInclusionForFD(unsigned fd) const {
    return m_includesMap.at(fd);
  }

  bool hasInclusions() { return !m_includesStack.empty(); }

  void startInclusion(const clang::FileEntry &fileEntry);

  void addRealInclDirective(clang::SourceRange range, clang::StringRef fileName,
                            const clang::FileEntryRef fileEntry,
                            bool isAngled) {
    currentInclusion()->addRealInclDirective(range, fileName,
                                             fileEntry.getUID(), isAngled);
  }

  void addGhostInclDirective(const clang::FileEntry *entry, Annotation &ann) {
    auto uid = entry->getUID();
    assert(m_includesMap.find(uid) != m_includesMap.end() &&
           "File has not been preprocessed and added to inclusion context");
    m_includesMap.at(uid).addGhostInclDirective(ann);
  }

  void endInclusion();

  void serializeTUInclDirectives(stubs::TU::Builder &builder,
                                 const clang::SourceManager &SM,
                                 AstSerializer &serializer) const;
};
} // namespace vf