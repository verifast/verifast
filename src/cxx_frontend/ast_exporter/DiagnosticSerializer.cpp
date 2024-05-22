#include "DiagnosticSerializer.h"
#include "LocationSerializer.h"
#include "clang/Basic/LangOptions.h"
#include "llvm/ADT/SmallString.h"

namespace vf {

void DiagnosticSerializer::HandleDiagnostic(
    clang::DiagnosticsEngine::Level level, const clang::Diagnostic &info) {
  clang::DiagnosticConsumer::HandleDiagnostic(level, info);
  if (level >= m_minLevel && info.hasSourceManager()) {
    llvm::SmallString<64> reason;
    info.FormatDiagnostic(reason);
    m_diags.emplace_back(info.getLocation(), reason.str(),
                         info.getSourceManager(), m_langOpts);
  }
}

void DiagnosticSerializer::BeginSourceFile(
    const clang::LangOptions &langOpts,
    const clang::Preprocessor *preprocessor) {
  m_langOpts = &langOpts;
}

void DiagnosticSerializer::EndSourceFile() { m_langOpts = nullptr; }

void DiagnosticSerializer::serialize(ListBuilder<stubs::Error> builder) const {
  assert(nbDiags() == builder.size() && "Target builder has wrong size");

  size_t i(0);
  for (const Diag &diag : m_diags) {
    stubs::Error::Builder errorBuilder = builder[i++];
    diag.serialize(errorBuilder);
  }
}

void DiagnosticSerializer::Diag::serialize(
    stubs::Error::Builder builder) const {
  const clang::LangOptions &langOpts =
      this->langOpts ? *this->langOpts : clang::LangOptions();
  LocationSerializer locSerializer(*sourceManager, langOpts);
  locSerializer.serialize(loc, builder.initLoc());
  builder.setReason(reason);
}

} // namespace vf