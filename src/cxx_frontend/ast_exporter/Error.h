#pragma once

#include "Location.h"
#include "stubs_ast.capnp.h"
#include "clang/Basic/FileEntry.h"
#include "clang/Basic/SourceLocation.h"

namespace vf {

class ErrorRange {
  LCF m_loc;
  bool m_valid;

public:
  ErrorRange(const clang::FullSourceLoc &fullLoc) {
    m_valid = fullLoc.isValid() && fullLoc.getFileEntry();
    if (m_valid) {
      m_loc.l = fullLoc.getLineNumber();
      m_loc.c = fullLoc.getColumnNumber();
      m_loc.f = fullLoc.getFileEntry()->getUID();
    }
  }

  void serialize(stubs::Loc::Builder builder) const {
    if (!m_valid) {
      return;
    }
    auto lexedBuilder = builder.initLexed();
    serializeSourcePos(lexedBuilder.initStart(), m_loc);
    serializeSourcePos(lexedBuilder.initEnd(), m_loc);
  }
};

struct Error {
  ErrorRange range;
  std::string reason;

  Error(ErrorRange range, llvm::StringRef reason) : range(range), reason(reason) {}

  void serialize(stubs::Error::Builder builder) const {
    auto locBuilder = builder.initLoc();
    range.serialize(locBuilder);
    builder.setReason(reason);
  }
};

} // namespace vf