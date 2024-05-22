#pragma once

#include "Serializer.h"
#include "stubs_ast.capnp.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"

namespace vf {

/**
 * @brief Serializer for source ranges. Recursively traverses macro expansions
 * during serialization in order to serialize a much location information as
 * possible.
 *
 */
class LocationSerializer
    : public Serializer<clang::SourceRange, stubs::Loc::Builder> {
public:
  /**
   * @brief Serializes a range to a location builder.
   *
   * @param range Range to serialize
   * @param builder Target location builder to serialize to
   */
  void serialize(clang::SourceRange range,
                 stubs::Loc::Builder builder) const override;

  LocationSerializer(const clang::SourceManager &sourceManager,
                     const clang::LangOptions &langOpts)
      : m_sourceManager(&sourceManager), m_langOpts(&langOpts) {}

private:
  /**
   * @brief Serialize a lexed source range. This does not check for macro
   * expansions. Token ranges are converted to source ranges that refer to the
   * beginning and end of the corresponding token.
   *
   * @param range Source range to serialize
   * @param builder Target lexed location builder to serialize to
   */
  void serializeLexedSourceRange(clang::SourceRange range,
                                 stubs::Loc::Lexed::Builder builder) const;

  /**
   * @brief Serialize the stack of locations through which a macro argument was
   * called.
   *
   * @param range Token range of the macro argument
   * @param builder Target location builder to serialize to
   */
  void serializeMacroArgCallStack(clang::CharSourceRange range,
                                  stubs::Loc::Builder builder) const;

  const clang::SourceManager *m_sourceManager;
  const clang::LangOptions *m_langOpts;
};

} // namespace vf