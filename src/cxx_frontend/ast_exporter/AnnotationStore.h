#pragma once
#include "Annotation.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
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
  using ann_v = std::vector<Annotation>;

  /**
   * Holds a sequence of VeriFast annotations.
   */
  struct AnnCont {
    unsigned int m_pos;
    ann_v m_anns;

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
     * @tparam Pred type of the predicate that is passed.
     * @tparam Cont type of the given container.
     * @param con container where all annotations that are retrieved from the
     * annotation container, are added to.
     * @param pred predicate that is used to check if the current annotation in
     * the annotation container should be retrieved.
     */
    template <class Pred, class Cont> void getWhile(Cont &con, Pred pred) {
      while (m_pos < m_anns.size()) {
        auto ann = m_anns.at(m_pos);
        if (pred(ann)) {
          con.push_back(ann);
          ++m_pos;
          continue;
        }
        return;
      }
    }

    /**
     * Retrieves all annotations in this annotation container and adds them to
     * the given container.
     * @tparam type of the given container.
     * @param con container where all annotation in this annotation container,
     * are added to.
     */
    template <class Cont> void getAll(Cont &con) {
      while (m_pos < m_anns.size()) {
        con.push_back(m_anns.at(m_pos));
      }
    }
  };

  std::unordered_map<unsigned, AnnCont> _annContainers;

  /**
   * Retrieves the annotation container that corresponds with the given
   * location. The unique identifier of the file entry that contains the given
   * location is used to retrieve the correct annotation store.
   * @param loc source location that is used to get the correct annotation
   * container.
   * @param SM source manager.
   */
  AnnCont &getCont(clang::SourceLocation loc, const clang::SourceManager &SM) {
    auto id = SM.getFileID(SM.getExpansionLoc(loc));
    auto entry = SM.getFileEntryForID(id);
    assert(entry);
    return _annContainers[entry->getUID()];
  }

public:
  explicit AnnotationStore() {}
  KJ_DISALLOW_COPY(AnnotationStore);

  /**
   * Add an annotation to this store.
   * @param ann annotation to add to this store. Be aware that the annotation
   * will be moved.
   * @param SM source manager.
   */
  void add(Annotation &&ann, const clang::SourceManager &SM) {
    getCont(ann.getRange().getBegin(), SM).add(std::move(ann));
  }

  /**
   * Retrieve every annotation before the given location.
   * @tparam Container type of the container where the retrieved annotations
   * will be added to.
   * @param con the container to add the annotations to.
   * @param loc location that comes from a specific file. Only the annotations
   * in that file that appear before this location are retrieved.
   * @param SM source manager.
   */
  template <class Container>
  void getUntilLoc(Container &con, clang::SourceLocation loc,
                   const clang::SourceManager &SM) {
    auto expLoc = SM.getFileLoc(loc);
    auto pred = [expLoc](const Annotation &ann) {
      // compare to 'begin' of range in case the end overlaps with the given loc
      return ann.getRange().getBegin() < expLoc;
    };
    getCont(expLoc, SM).getWhile(con, pred);
  }

  /**
   * Retrieve all annotations in the file that corresponds to the
   * given location.
   * @tparam Container type of the container where the retrieved annotations
   * will be added to.
   * @param currentLoc location that comes from a specific file. It may be you
   * 'current' location in the file. The location is used to retrieve the
   * annotations from the correct file.
   * @param con the container to add the annotations to.
   * @param SM source manager.
   */
  template <class Container>
  void getAll(const clang::SourceLocation currentLoc, Container &con,
              const clang::SourceManager &SM) {
    getCont(SM.getFileLoc(currentLoc), SM).getAll(con);
  }

  template <class Container> void getAll(unsigned fileUID, Container &con) {
    _annContainers[fileUID].getAll(con);
  }

  /**
   * Retrieves the next contract from the store. The contract that
   * is retrieved comes from the file that corresponds with the given location.
   * @tparam Container type of the container where the retrieved annotations
   * will be added to.
   * @param currentLoc location that comes from a specific file. It may be you
   * 'current' location in the file. The location is used to retrieve the
   * annotations from the correct file.
   * @param con the container to add the annotations to.
   * @param SM source manager.
   * @param loc optional location that represents the start of a body. E.g.,
   * when you want to retrieve the contract of a function implementation, you
   * can pass the the location of the start of the body. Otherwise an attempt
   * will be done to get a best match for a function contract.
   */
  template <class Container>
  void getContract(const clang::SourceLocation currentLoc, Container &con,
                   const clang::SourceManager &SM,
                   clang::SourceLocation loc = {}) {
    if (loc.isValid()) {
      return getUntilLoc(con, loc, SM);
    }
    bool first = true;
    auto pred = [&first](const Annotation &ann) {
      bool result = ann.isContractClauseLike() && first == ann.isNewSeq();
      first = false;
      return result;
    };
    getCont(SM.getFileLoc(currentLoc), SM).getWhile(con, pred);
  }

  llvm::Optional<clang::SourceRange>
  queryTruncatingAnnotation(const clang::SourceLocation currentLoc,
                            const clang::SourceManager &SM) {
    auto pred = [&currentLoc](const Annotation &ann) {
      // compare to 'begin' of range in case the end overlaps with the given
      // currentLoc
      return ann.getRange().getBegin() < currentLoc && ann.isTruncating();
    };
    llvm::SmallVector<Annotation, 1> query;
    getCont(SM.getFileLoc(currentLoc), SM).getWhile(query, pred);
    llvm::Optional<clang::SourceRange> result;
    if (query.empty()) {
      return result;
    }
    result.emplace(query.front().getRange());
    return result;
  }
};
} // namespace vf