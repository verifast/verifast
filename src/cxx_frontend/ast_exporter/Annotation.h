#pragma once
#include "kj/common.h"
#include "clang/AST/Decl.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/ADT/Optional.h"
#include <unordered_map>

namespace vf {

class Text {
  clang::SourceRange m_range;
  std::string m_text;

public:
  Text(clang::SourceRange range, llvm::StringRef text)
      : m_range(range), m_text(text) {}

  clang::SourceRange getRange() const { return m_range; }

  llvm::StringRef getText() const { return m_text; }

  virtual ~Text() {}
};

/**
 * Represents a VeriFast annotation in the source code.
 */
class Annotation : public Text {
public:
  enum Kind {
    Ann_Unknown,
    Ann_ContractClause,
    Ann_Truncating,
    Ann_Include,
    Ann_other,
  };

private:
  Kind m_kind;
  bool m_isNewSeq;

public:
  Annotation(clang::SourceRange range, llvm::StringRef text, Kind kind,
             bool isNewSeq)
      : Text(range, text), m_kind(kind), m_isNewSeq(isNewSeq) {}

public:
  /**
   * @return whether or not this annotation can appear in a contract. I.e., the
   annotation starts with 'requires, 'ensures', 'terminates', ':', or
   'non_ghost_callers_only'. White space characters are not taken into account.
   */
  bool isContractClauseLike() const { return m_kind == Ann_ContractClause; }

  /**
   * @return wether or not this annotation starts a new sequence of annotations.
   * I.e., the lines between this annotation and the previous one do not only
   * contain comments and/or white space.
   */
  bool isNewSeq() const { return m_isNewSeq; }

  /**
   * @return wether or not this annotation is a truncating expression.
   */
  bool isTruncating() const { return m_kind == Ann_Truncating; }

  /**
   * @return wether or not this annotation in an include directive.
   */
  bool isInclude() const { return m_kind == Ann_Include; }
};

/**
 * Transforms the given text into an annotation if it represents one.
 * @param range the source range of the text.
 * @param text the text that may represent an annotation. This method assumes
 * that the given text is a valid C++ comment.
 * @param newSeq whether or not this annotation starts a new sequence.
 * @return an optional of an annotation.
 */
llvm::Optional<Annotation> annotationOf(clang::SourceRange range,
                                        llvm::StringRef text, bool isNewSeq);

/**
 * Container that owns all VeriFast annotations encountered during parsing.
 * More specifically, it acts as a map from C++ files to containers of
 * annotations. The store allows to add annotations and to retrieve them.
 * Note that an annotation can only be retrieved once. The store keeps track of
 * a current index to know which annotations have already been retrieved.
 */
class AnnotationStore {
  using AnnotationPred = llvm::function_ref<bool(const Annotation &)>;

  /**
   * Holds a sequence of VeriFast annotations.
   */
  struct AnnotationContainer {
    unsigned int m_pos;
    std::vector<Annotation> m_annotations;

    explicit AnnotationContainer() : m_pos(0) {}

    /**
     * Moves the given annotation in this store.
     * @param ann the annotation that will be moved.
     */
    void add(Annotation &&ann) { m_annotations.emplace_back(std::move(ann)); }

    /**
     * Retrieve every annotation from this container while the given predicate
     * holds for the annotation that is currently at the front of this
     * container. The annotations that are retrieved from the container are
     * added to a given container.
     * @param container container where all annotations that are retrieved from
     * the annotation container, are added to.
     * @param pred predicate that is used to check if the current annotation in
     * the annotation container should be retrieved.
     */
    void getWhile(llvm::SmallVectorImpl<Annotation> &container,
                  AnnotationPred pred);

    /**
     * Retrieves all annotations in this annotation container and adds them to
     * the given container.
     * @param container container where all annotation in this annotation
     * container, are added to.
     */
    void getAll(llvm::SmallVectorImpl<Annotation> &container);
  };

  std::unordered_map<unsigned, AnnotationContainer> m_annContainers;
  llvm::SmallVector<Text> m_failDirectives;

  /**
   * Retrieves the annotation container that corresponds with the given
   * location. The unique identifier of the file entry that contains the given
   * location is used to retrieve the correct annotation store.
   * @param loc source location that is used to get the correct annotation
   * container.
   * @param SM source manager.
   */
  AnnotationContainer &getContainer(const clang::FileEntry *entry) {
    return m_annContainers[entry->getUID()];
  }

  void getContract(const clang::FileEntry *entry,
                   llvm::SmallVectorImpl<Annotation> &container,
                   const clang::SourceManager &SM,
                   clang::SourceLocation bodyStartLoc);

public:
  explicit AnnotationStore() {}
  KJ_DISALLOW_COPY(AnnotationStore);

  /**
   * Add an annotation to this store.
   * @param ann annotation to add to this store. Be aware that the annotation
   * will be moved.
   * @param SM source manager.
   */
  void add(Annotation &&ann, const clang::SourceManager &SM);

  void addFailDirective(Text &&directive) {
    m_failDirectives.emplace_back(std::move(directive));
  }

  const llvm::ArrayRef<Text> getFailDirectives() const {
    return m_failDirectives;
  }

  /**
   * Retrieve every annotation before the given location.
   * @param container the container to add the annotations to.
   * @param loc location that comes from a specific file. Only the annotations
   * in that file that appear before this location are retrieved.
   * @param SM source manager.
   */
  void getUntilLoc(llvm::SmallVectorImpl<Annotation> &container,
                   const clang::SourceLocation loc,
                   const clang::SourceManager &SM);

  /**
   * Retrieve all annotations in the file that corresponds to the
   * given location.
   */
  void getAll(const clang::FileEntry *entry,
              llvm::SmallVectorImpl<Annotation> &container);

  void getContract(const clang::FunctionDecl *decl,
                   llvm::SmallVectorImpl<Annotation> &container,
                   const clang::SourceManager &SM);

  void guessContract(const clang::FileEntry *entry,
                     llvm::SmallVectorImpl<Annotation> &container,
                     const clang::SourceManager &SM,
                     clang::SourceLocation maxEndLoc);

  llvm::Optional<clang::SourceRange>
  queryTruncatingAnnotation(const clang::SourceLocation currentLoc,
                            const clang::SourceManager &SM);

  void getGhostIncludeSequence(const clang::FileEntry *entry,
                               llvm::SmallVectorImpl<Annotation> &container);
};
} // namespace vf