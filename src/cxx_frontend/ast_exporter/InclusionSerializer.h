#pragma once
#include "ASTSerializer.h"
#include "InclusionContext.h"
#include "llvm/ADT/DenseMap.h"

namespace vf {

/**
 * @brief Specialized serializer for inclusions.
 * 
 */
class InclusionSerializer
    : public Serializer<const Inclusion &, ListBuilder<stubs::Include>> {
public:
  void serialize(const Inclusion &inclusion,
                 ListBuilder<stubs::Include> builder) const override;

  InclusionSerializer(const ASTSerializer &serializer,
                      const InclusionContext &context,
                      const llvm::SmallDenseMap<unsigned, clang::SourceLocation>
                          &firstDeclLocMap)
      : m_serializer(&serializer), m_context(&context),
        m_firstDeclLocMap(&firstDeclLocMap) {}

  const ASTSerializer &getASTSerializer() const { return *m_serializer; }

  const InclusionContext &getInclusionContext() const { return *m_context; }

private:
  clang::SourceLocation
  getFirstDeclLocInFile(const clang::FileEntry *fileEntry) const;

  const ASTSerializer *m_serializer;
  const InclusionContext *m_context;
  const llvm::SmallDenseMap<unsigned, clang::SourceLocation> *m_firstDeclLocMap;
};

} // namespace vf