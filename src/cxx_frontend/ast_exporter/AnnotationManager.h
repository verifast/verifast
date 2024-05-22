#pragma once
#include "Annotation.h"
#include "Text.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/TypeLoc.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"

namespace vf {

/// @brief  Alias for a reference to an array of annotations.
using AnnotationsRef = llvm::ArrayRef<Annotation>;

/**
 * @brief Manages storage and retrieval of annotations and fail directives.
 *
 * This class provides methods to add, analyze, and retrieve annotations and
 * fail directives. Note that adding new annotations may invalidate any
 * references to previously retrieved annotations or fail directives.
 */
class AnnotationManager {
public:
  /**
   * @brief Analyzes the given text within a specified source range.
   *
   * @param range The source range within which the text resides.
   * @param text The text to analyze.
   * @return An optional Annotation if the analysis is successful.
   */
  std::optional<Annotation> analyzeText(clang::SourceRange range,
                                        std::string_view text);

  /**
   * @brief Adds a new annotation to the manager.
   *
   * @param annotation The annotation to add.
   */
  void addAnnotation(Annotation &&annotation);

  /**
   * @brief Adds a new fail directive to the manager.
   *
   * @param text The text of the fail directive to add.
   */
  void addFailDirective(Text &&text);

  /**
   * @brief Retrieves the contract annotations for the given function
   * declaration.
   *
   * @param decl The function declaration whose contract annotations are to be
   * retrieved.
   * @return A reference to an array of annotations.
   */
  AnnotationsRef getContract(const clang::FunctionDecl *decl) const;

  /**
   * @brief Retrieves the contract annotations for the given function prototype
   * type location.
   *
   * @param protoType The function prototype type location whose contract
   * annotations are to be retrieved.
   * @return A reference to an array of annotations.
   */
  AnnotationsRef getContract(clang::FunctionProtoTypeLoc protoType) const;

  /**
   * @brief Retrieves the annotation associated with a truncating expression.
   *
   * @param expr The expression whose truncating annotation is to be retrieved.
   * @return A pointer to the annotation, or nullptr if not found.
   */
  const Annotation *getTruncating(const clang::Expr *expr) const;

  /**
   * @brief Retrieves all fail directives.
   *
   * @return A reference to an array of fail directives.
   */
  llvm::ArrayRef<Text> getFailDirectives() const;

  /**
   * @brief Retrieves all annotations for the given file entry.
   *
   * @param entry The file entry whose annotations are to be retrieved.
   * @return A reference to an array of annotations.
   */
  AnnotationsRef getAll(const clang::FileEntry *entry) const;

  /**
   * @brief Retrieves annotations within a specified source range.
   *
   * @param begin The starting location of the range. Can be invalid, in which
   * case the starting location will not be taken into account.
   * @param end The ending location of the range. Can be invalid, in which case
   * the ending location will not be taken into account.
   * @return A reference to an array of annotations within the range.
   */
  AnnotationsRef getInRange(clang::SourceLocation begin,
                            clang::SourceLocation end) const;

  /**
   * @brief Retrieves leading ghost include annotations for the given file
   * entry.
   *
   * @param entry The file entry whose leading include annotations are to be
   * retrieved.
   * @return A reference to an array of annotations.
   */
  AnnotationsRef getLeadingIncludes(const clang::FileEntry *entry) const;

  /**
   * @brief Retrieves annotations that occur after a specified source location.
   *
   * @param beginLoc The source location after which annotations are to be
   * retrieved.
   * @return A reference to an array of annotations.
   */
  AnnotationsRef getSequenceAfterLoc(clang::SourceLocation beginLoc) const;

  /**
   * @brief Constructs an AnnotationManager.
   *
   * @param sourceManager The source manager used to manage source locations.
   * @param langOpts The language options used for analysis.
   */
  AnnotationManager(const clang::SourceManager &sourceManager,
                    const clang::LangOptions &langOpts)
      : m_sourceManager(&sourceManager), m_langOpts(&langOpts) {}

private:
  /**
   * @brief Retrieves the contract annotations starting from a specified source
   * location.
   *
   * @param startLoc The starting location of the contract annotations.
   * @return A reference to an array of annotations.
   */
  AnnotationsRef getContract(clang::SourceLocation startLoc) const;

  ///< Map of annotations indexed by file.
  llvm::SmallDenseMap<unsigned, llvm::SmallVector<Annotation>> m_annotationMap;
  ///< Map of fail directives indexed by file.
  llvm::SmallDenseMap<unsigned, llvm::SmallVector<Annotation>> m_directivesMap;
  ///< List of all fail directives.
  llvm::SmallVector<Text> m_failDirectives;
  const clang::SourceManager *m_sourceManager;
  const clang::LangOptions *m_langOpts;
};

} // namespace vf