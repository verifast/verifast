#pragma once

#include "Error.h"
#include "clang/Basic/Diagnostic.h"

namespace vf {

class DiagnosticCollectorConsumer : public clang::DiagnosticConsumer {
  clang::DiagnosticsEngine::Level m_minLevel;
  clang::SmallVector<Error> m_errors;

public:
  explicit DiagnosticCollectorConsumer(clang::DiagnosticsEngine::Level minLevel)
      : m_minLevel(minLevel) {}

  clang::DiagnosticsEngine::Level getMinLevel() const { return m_minLevel; }

  clang::ArrayRef<Error> getErrors() const { return m_errors; }

  size_t nbErrors() const { return m_errors.size(); }

  virtual bool IncludeInDiagnosticCounts() const override { return true; }

  virtual void HandleDiagnostic(clang::DiagnosticsEngine::Level level,
                                const clang::Diagnostic &info) override {
    if (level >= m_minLevel) {
      clang::StoredDiagnostic diag(level, info);
      ErrorRange range(diag.getLocation());
      m_errors.emplace_back(range, diag.getMessage());
    }
  }
};

} // namespace vf