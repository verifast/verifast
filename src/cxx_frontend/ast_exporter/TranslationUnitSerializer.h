#pragma once
#include "DeclSerializer.h"
#include "InclusionContext.h"
#include "NodeListSerializer.h"
#include "Serializer.h"
#include "clang/AST/Decl.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/IndexedMap.h"

namespace vf {

/**
 * @brief Specialized serializer for translation units.
 *
 */
class TranslationUnitSerializer
    : public Serializer<const clang::TranslationUnitDecl *,
                        stubs::TU::Builder> {
public:
  void serialize(const clang::TranslationUnitDecl *decl,
                 stubs::TU::Builder builder) const override;

  TranslationUnitSerializer(const clang::ASTContext &ASTContext,
                            const AnnotationManager &annotationManager,
                            const InclusionContext &inclusionContext,
                            capnp::Orphanage orphanage, bool skipImplicitDecls)
      : m_ASTContext(&ASTContext), m_annotationManager(&annotationManager),
        m_inclusionContext(&inclusionContext),
        m_serializer(ASTContext, annotationManager, skipImplicitDecls),
        m_orphanage(orphanage) {}

private:
  /**
   * @brief Get declaration list serializer for the given file.
   *
   * @param uid Unique identifier of the file for which the serializer has to be
   * returned.
   * @return Declaration list serializer for the file.
   */
  DeclListSerializer &getDeclSerializer(unsigned uid) const;

  /**
   * @brief Serialize a declaration in the translation unit associated with this
   * serializer.
   *
   * Updates the mapping of the declaration's file to the source location of the
   * first declaration in that file if needed.
   *
   * Serializes annotation declarations that appear before the given declaration
   * if it is the first declaration in its file.
   *
   * Serializes declarations tha appear after the given declaration and before
   * the next declaration (or end of file if the given declaration is the last
   * declaration in its file).
   *
   * @param decl Declaration to serialize.
   */
  void serializeDecl(const clang::Decl *decl) const;

  /**
   * @brief Serialize a file of the translation unit.
   *
   * Retrieves the declaration list serializer associated with the given file
   * and adopts all its serialized declarations to the target builder of the
   * file. Hence, all declarations must have been serialized before using this
   * method.
   *
   * @param fileEntry Entry of the file to serialize.
   * @param builder Target builder to serialize to.
   */
  void serializeFile(const clang::FileEntry *fileEntry,
                     stubs::File::Builder builder) const;

  const clang::ASTContext *m_ASTContext;
  const AnnotationManager *m_annotationManager;
  const InclusionContext *m_inclusionContext;
  ASTSerializer m_serializer;
  capnp::Orphanage m_orphanage;

  ///< Mapping from files to declaration list serializers
  mutable llvm::SmallDenseMap<unsigned, DeclListSerializer> m_declsMap;
  ///< Mapping from files to the location of the first declaration in that file.
  mutable llvm::SmallDenseMap<unsigned, clang::SourceLocation>
      m_firstDeclLocMap;
};

} // namespace vf