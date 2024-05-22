#include "LocationSerializer.h"
#include "Location.h"
#include "clang/Lex/Lexer.h"

namespace vf {

void serializeSourcePos(stubs::Loc::SrcPos::Builder builder, Location loc) {
  loc.serialize(builder);
}

void LocationSerializer::serialize(clang::SourceRange range,
                                   stubs::Loc::Builder builder) const {
  auto begin = range.getBegin();
  clang::SourceLocation end = range.getEnd();

  // Range comes from macro expansion of one token
  if (begin == end && begin.isMacroID()) {
    stubs::Loc::MacroExp::Builder expBuilder = builder.initMacroExp();
    stubs::Loc::Builder callSiteBuilder = expBuilder.initCallSite();
    stubs::Loc::Builder bodyTokenBuilder = expBuilder.initBodyToken();

    // Argument expansion from function-like macro
    if (m_sourceManager->isMacroArgExpansion(begin)) {
      clang::SourceLocation immediateExpBegin =
          m_sourceManager->getImmediateExpansionRange(begin).getBegin();

      serializeMacroArgCallStack(
          m_sourceManager->getImmediateExpansionRange(begin), callSiteBuilder);

      stubs::Loc::MacroParamExp::Builder paramExpBuilder =
          bodyTokenBuilder.initMacroParamExp();
      stubs::Loc::Builder paramBuilder = paramExpBuilder.initParam();
      stubs::Loc::Builder argTokenBuilder = paramExpBuilder.initArgToken();

      serialize(m_sourceManager->getSpellingLoc(immediateExpBegin),
                paramBuilder);
      serialize(m_sourceManager->getImmediateMacroCallerLoc(begin),
                argTokenBuilder);
      return;
    }

    // Simple expansion
    serialize(m_sourceManager->getImmediateMacroCallerLoc(begin),
              callSiteBuilder);
    serialize(m_sourceManager->getSpellingLoc(begin), bodyTokenBuilder);
    return;
  }

  // Range represents one token not coming from a macro expansion, multiple
  // tokens or concatenation of macro tokens
  serializeLexedSourceRange(range, builder.initLexed());
}

void LocationSerializer::serializeLexedSourceRange(
    clang::SourceRange range, stubs::Loc::Lexed::Builder builder) const {
  clang::CharSourceRange charRange =
      clang::Lexer::getAsCharRange(range, *m_sourceManager, *m_langOpts);
  std::optional<Location> beginOpt =
      ofSourceLocation(charRange.getBegin(), *m_sourceManager);
  std::optional<Location> endOpt =
      ofSourceLocation(charRange.getEnd(), *m_sourceManager);

  if (beginOpt) {
    serializeSourcePos(builder.initStart(), *beginOpt);
  }
  if (endOpt) {
    serializeSourcePos(builder.initEnd(), *endOpt);
  }
}

void LocationSerializer::serializeMacroArgCallStack(
    clang::CharSourceRange range, stubs::Loc::Builder builder) const {
  clang::SourceLocation begin = range.getBegin();
  clang::CharSourceRange expRange =
      m_sourceManager->getImmediateExpansionRange(begin);
  clang::SourceLocation immediateMacroCallerLoc =
      m_sourceManager->getSpellingLoc(
          m_sourceManager->getImmediateMacroCallerLoc(begin));

  // Traverse stack of macro calls recursively
  if (expRange.getBegin().isMacroID()) {
    stubs::Loc::MacroExp::Builder expBuilder = builder.initMacroExp();
    stubs::Loc::Builder callSiteBuilder = expBuilder.initCallSite();
    stubs::Loc::Builder bodyTokenBuilder = expBuilder.initBodyToken();

    serializeMacroArgCallStack(expRange, callSiteBuilder);
    serializeLexedSourceRange(immediateMacroCallerLoc,
                              bodyTokenBuilder.initLexed());
    return;
  }

  serializeLexedSourceRange(immediateMacroCallerLoc, builder.initLexed());
}
} // namespace vf