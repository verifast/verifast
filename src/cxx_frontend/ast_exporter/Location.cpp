#include "Location.h"
#include "clang/Lex/Lexer.h"

namespace vf {

bool decomposeLocToLCF(const clang::SourceLocation loc,
                       const clang::SourceManager &SM, LCF &lcf) {
  if (loc.isInvalid()) {
    return false;
  }
  auto decLoc = SM.getDecomposedLoc(SM.getSpellingLoc(loc));
  auto fileEntry = SM.getFileEntryForID(decLoc.first);

  if (!fileEntry)
    return false;

  auto uid = fileEntry->getUID();
  auto line = SM.getLineNumber(decLoc.first, decLoc.second);
  auto col = SM.getColumnNumber(decLoc.first, decLoc.second);
  lcf.l = line;
  lcf.c = col;
  lcf.f = uid;
  return true;
}

void serializeSourcePos(stubs::Loc::SrcPos::Builder builder, LCF lcf) {
  builder.setL(lcf.l);
  builder.setC(lcf.c);
  builder.setFd(lcf.f);
}

void serializeLexedSourceRange(stubs::Loc::Lexed::Builder builder,
                               clang::SourceRange range,
                               const clang::SourceManager &SM,
                               const clang::LangOptions &langOpts) {
  auto charRange = clang::Lexer::getAsCharRange(range, SM, langOpts);
  LCF lcf;
  if (decomposeLocToLCF(charRange.getBegin(), SM, lcf)) {
    serializeSourcePos(builder.initStart(), lcf);
  }
  if (decomposeLocToLCF(charRange.getEnd(), SM, lcf)) {
    serializeSourcePos(builder.initEnd(), lcf);
  }
}

void serializeMacroArgCallStack(stubs::Loc::Builder builder,
                                clang::CharSourceRange range,
                                const clang::SourceManager &SM,
                                const clang::LangOptions &langOpts) {
  auto begin = range.getBegin();
  auto expRange = SM.getImmediateExpansionRange(begin);
  auto immediateMacroCallerLoc =
      SM.getSpellingLoc(SM.getImmediateMacroCallerLoc(begin));

  // Traverse stack of macro calls recursively
  if (expRange.getBegin().isMacroID()) {
    auto expBuilder = builder.initMacroExp();
    auto callSiteBuilder = expBuilder.initCallSite();
    auto bodyTokenBuilder = expBuilder.initBodyToken();

    serializeMacroArgCallStack(callSiteBuilder, expRange, SM, langOpts);
    serializeLexedSourceRange(bodyTokenBuilder.initLexed(),
                              immediateMacroCallerLoc, SM, langOpts);
    return;
  }

  serializeLexedSourceRange(builder.initLexed(), immediateMacroCallerLoc, SM,
                            langOpts);
}

void serializeSourceRange(stubs::Loc::Builder builder, clang::SourceRange range,
                          const clang::SourceManager &SM,
                          const clang::LangOptions &langOpts) {
  auto begin = range.getBegin();
  auto end = range.getEnd();

  // Range comes from macro expansion of one token
  if (begin == end && begin.isMacroID()) {
    auto expBuilder = builder.initMacroExp();
    auto callSiteBuilder = expBuilder.initCallSite();
    auto bodyTokenBuilder = expBuilder.initBodyToken();

    // Argument expansion from function-like macro
    if (SM.isMacroArgExpansion(begin)) {
      auto immediateExpBegin = SM.getImmediateExpansionRange(begin).getBegin();

      serializeMacroArgCallStack(
          callSiteBuilder, SM.getImmediateExpansionRange(begin), SM, langOpts);

      auto paramExpBuilder = bodyTokenBuilder.initMacroParamExp();
      auto paramBuilder = paramExpBuilder.initParam();
      auto argTokenBuilder = paramExpBuilder.initArgToken();

      serializeSourceRange(paramBuilder, SM.getSpellingLoc(immediateExpBegin),
                           SM, langOpts);
      serializeSourceRange(argTokenBuilder,
                           SM.getImmediateMacroCallerLoc(begin), SM, langOpts);
      return;
    }

    // Simple expansion
    serializeSourceRange(callSiteBuilder, SM.getImmediateMacroCallerLoc(begin),
                         SM, langOpts);
    serializeSourceRange(bodyTokenBuilder, SM.getSpellingLoc(begin), SM,
                         langOpts);
    return;
  }

  // Range represents one token not coming from a macro expansion, multiple
  // tokens or concatenation of macro tokens
  serializeLexedSourceRange(builder.initLexed(), range, SM, langOpts);
}

const clang::FileEntry *getFileEntry(const clang::SourceLocation loc,
                                     const clang::SourceManager &SM) {
  auto id = SM.getFileID(SM.getExpansionLoc(loc));
  return SM.getFileEntryForID(id);
}

} // namespace vf