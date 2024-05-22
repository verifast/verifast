#include "AnnotationManager.h"
#include "Location.h"
#include "clang/Lex/Lexer.h"

namespace vf {

void AnnotationManager::addAnnotation(Annotation &&annotation) {
  const clang::FileEntry *fileEntry =
      fileEntryOfLoc(annotation.getRange().getBegin(), *m_sourceManager);
  unsigned fileId = fileEntry->getUID();

  llvm::SmallVector<Annotation> &annotations =
      annotation.is(Annotation::Ann_Include) ? m_directivesMap[fileId]
                                             : m_annotationMap[fileId];

  if (!annotations.empty()) {
    assert(annotation.getRange().getBegin() >
               annotations.back().getRange().getEnd() &&
           "Annotation in wrong order");
  }
  annotations.emplace_back(annotation);
}

void AnnotationManager::addFailDirective(Text &&failDirective) {
  m_failDirectives.emplace_back(failDirective);
}

AnnotationsRef
AnnotationManager::getAll(const clang::FileEntry *fileEntry) const {
  if (!fileEntry) {
    return {};
  }

  auto it = m_annotationMap.find(fileEntry->getUID());

  if (it == m_annotationMap.end()) {
    return {};
  }

  return it->getSecond();
}

llvm::ArrayRef<Text> AnnotationManager::getFailDirectives() const {
  return m_failDirectives;
}

const Annotation *
AnnotationManager::getTruncating(const clang::Expr *expr) const {
  AnnotationsRef leadingAnnotations = getInRange({}, expr->getBeginLoc());

  if (leadingAnnotations.empty()) {
    return {};
  }

  const Annotation &back = leadingAnnotations.back();

  if (back.is(Annotation::Kind::Ann_Truncating) &&
      back.getNextTokenLoc() == expr->getBeginLoc()) {
    return &back;
  }

  return {};
}

AnnotationsRef AnnotationManager::getInRange(clang::SourceLocation begin,
                                             clang::SourceLocation end) const {
  if (begin.isInvalid() && end.isInvalid()) {
    return {};
  }

  clang::SourceLocation loc = begin.isValid() ? begin : end;
  const clang::FileEntry *entry = fileEntryOfLoc(loc, *m_sourceManager);

  AnnotationsRef annotations = getAll(entry);

  if (begin.isValid()) {
    annotations = annotations.drop_while([begin](const Annotation &annotation) {
      return annotation.getRange().getEnd() < begin;
    });
  }

  if (end.isValid()) {
    annotations = annotations.take_while([end](const Annotation &annotation) {
      return annotation.getRange().getEnd() <= end;
    });
  }

  return annotations;
}

AnnotationsRef
AnnotationManager::getLeadingIncludes(const clang::FileEntry *entry) const {
  if (!entry) {
    return {};
  }

  auto it = m_directivesMap.find(entry->getUID());
  if (it == m_directivesMap.end()) {
    return {};
  }

  return it->getSecond();
}

AnnotationsRef
AnnotationManager::getSequenceAfterLoc(clang::SourceLocation beginLoc) const {
  if (beginLoc.isInvalid()) {
    return {};
  }

  clang::Token nextToken(getNextToken(beginLoc, *m_sourceManager, *m_langOpts));

  return getInRange(beginLoc, nextToken.getLocation());
}

AnnotationsRef
AnnotationManager::getContract(clang::SourceLocation startLoc) const {
  if (startLoc.isInvalid()) {
    return {};
  }

  clang::Token nextToken(getNextToken(startLoc, *m_sourceManager, *m_langOpts));
  clang::SourceLocation endLoc = nextToken.getLocation();

  AnnotationsRef annotations = getInRange(startLoc, endLoc);
  return annotations.take_while(
      Annotation::Predicate<Annotation::Kind::Ann_ContractClause>());
}

AnnotationsRef
AnnotationManager::getContract(const clang::FunctionDecl *decl) const {
  if (decl->isImplicit()) {
    return {};
  }
  if (decl->isThisDeclarationADefinition()) {
    return getInRange(decl->getTypeSpecEndLoc(),
                      decl->getBody()->getBeginLoc());
  }

  clang::Token nextToken(expectNextToken(decl->getEndLoc(), *m_sourceManager,
                                         *m_langOpts, clang::tok::semi));
  return getContract(nextToken.getLocation());
}

AnnotationsRef
AnnotationManager::getContract(clang::FunctionProtoTypeLoc protoType) const {
  if (protoType.isNull()) {
    return {};
  }

  clang::SourceLocation rParenLoc = protoType.getRParenLoc();
  clang::Token nextToken(expectNextToken(rParenLoc, *m_sourceManager,
                                         *m_langOpts, clang::tok::semi));

  return getContract(nextToken.getLocation());
}

namespace {

// Check for ghost symbols. `/*@*/` is allowed so we don't silently ignore it
// and VeriFast can throw a parse error.
bool isAnnotationLike(std::string_view text) {
  std::string_view::iterator begin = text.begin();
  std::string_view::iterator end = text.end();
  return text.size() > 3 && *(begin + 2) == '@' &&
         (*(begin + 1) == '/' || *(end - 3) == '@');
}

class GhostCodeAnalyzer {
public:
  explicit GhostCodeAnalyzer(std::string_view text)
      : m_text(text), m_pos(text.begin()),
        m_kind(Annotation::Kind::Ann_Unknown) {}

  Annotation::Kind getKind() {
    if (kindIsNotUnknown())
      return m_kind;
    if (isTruncating() || isContractClauseLike() || isInclude())
      return m_kind;

    m_kind = Annotation::Kind::Ann_Other;
    return m_kind;
  }

private:
  void skipWhitespace() {
    for (; m_pos != m_text.end() && std::isspace(*m_pos); ++m_pos)
      ;
  }

  bool startsWith(std::string_view prefix) {
    std::string_view::iterator pos = prefix.begin();
    for (; m_pos != m_text.end() && pos != prefix.end() && *m_pos == *pos;
         ++m_pos, ++pos)
      ;
    return pos == prefix.end();
  }

  bool kindIsNotUnknown() { return m_kind != Annotation::Kind::Ann_Unknown; }

  bool isContractClauseLike() {
    if (kindIsNotUnknown())
      return m_kind == Annotation::Kind::Ann_ContractClause;

    for (std::string_view prefix : m_checks) {
      m_pos = m_text.begin() + 3;
      skipWhitespace();
      if (startsWith(prefix)) {
        m_kind = Annotation::Kind::Ann_ContractClause;
        return true;
      }
    }
    return false;
  }

  bool isTruncating() {
    if (kindIsNotUnknown())
      return m_kind == Annotation::Kind::Ann_Truncating;

    m_pos = m_text.begin() + 3;

    skipWhitespace();
    if (!startsWith("truncating")) {
      return false;
    }

    skipWhitespace();
    if (m_pos == m_text.end()) {
      m_kind = Annotation::Kind::Ann_Truncating;
      return true;
    }

    if (startsWith("@*/")) {
      m_kind = Annotation::Kind::Ann_Truncating;
      return true;
    }

    return false;
  }

  bool isInclude() {
    if (kindIsNotUnknown())
      return m_kind == Annotation::Kind::Ann_Include;

    m_pos = m_text.begin() + 3;

    skipWhitespace();
    if (startsWith("#include")) {
      m_kind = Annotation::Kind::Ann_Include;
      return true;
    }

    return false;
  }

  std::string_view m_text;
  std::string_view::iterator m_pos;
  Annotation::Kind m_kind;

  std::string_view static constexpr m_checks[] = {
      "requires", "ensures", "terminates", ":", "non_ghost_callers_only"};
};
} // namespace

std::optional<Annotation>
AnnotationManager::analyzeText(clang::SourceRange range,
                               std::string_view text) {
  if (!isAnnotationLike(text)) {
    return {};
  }

  GhostCodeAnalyzer gca(text);
  Annotation::Kind kind = gca.getKind();

  clang::Token nextToken(
      getNextToken(range.getBegin(), *m_sourceManager, *m_langOpts));
  clang::SourceLocation nextTokenLoc = nextToken.getLocation();

  return std::make_optional<Annotation>(kind, range, text, nextTokenLoc);
}

} // namespace vf