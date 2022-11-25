#pragma once
#include "Annotation.h"
#include "clang/AST/Decl.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/ADT/STLForwardCompat.h"
#include "llvm/ADT/SmallVector.h"
#include <kj/common.h>
#include <unordered_map>
#include <vector>

namespace vf {

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
  struct AnnCont {
    unsigned int m_pos;
    std::vector<Annotation> m_anns;

    explicit AnnCont() : m_pos(0) {}

    /**
     * Moves the given annotation in this store.
     * @param ann the annotation that will be moved.
     */
    void add(Annotation &&ann) { m_anns.emplace_back(std::move(ann)); }

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

  std::unordered_map<unsigned, AnnCont> m_annContainers;
  llvm::SmallVector<Text> m_failDirectives;

  /**
   * Retrieves the annotation container that corresponds with the given
   * location. The unique identifier of the file entry that contains the given
   * location is used to retrieve the correct annotation store.
   * @param loc source location that is used to get the correct annotation
   * container.
   * @param SM source manager.
   */
  AnnCont &getCont(const clang::FileEntry *entry) {
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
                               llvm::SmallVectorImpl<Annotation> &container,
                               const clang::SourceManager &SM);
};
} // namespace vf
