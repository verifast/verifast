#pragma once

#include "Util.h"
#include "stubs_ast.capnp.h"
#include "clang/Basic/SourceLocation.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/raw_ostream.h"

namespace vf {

class ErrorRange {
  LCF m_begin;
  LCF m_end;
  bool m_valid;

public:
  ErrorRange(clang::SourceRange range, const clang::SourceManager &SM) {
    decomposeLocToLCF(range.getBegin(), SM, m_begin);
    decomposeLocToLCF(range.getEnd(), SM, m_end);
    m_valid = range.isValid();
  }

  void serialize(stubs::Loc::Builder &builder) const;
};

struct Error {
  ErrorRange range;
  std::string reason;

  Error(ErrorRange range, std::string &reason) : range(range), reason(reason) {}
};

class ErrorBuilder {
  ErrorRange m_range;
  std::string m_error;
  llvm::raw_string_ostream m_error_stream;

public:
  explicit ErrorBuilder(clang::SourceRange range, const clang::SourceManager &SM)
      : m_range(range, SM), m_error_stream(m_error) {}

  operator Error() { return Error(m_range, m_error_stream.str()); }

  template <class T> ErrorBuilder &operator<<(const T &t) {
    m_error_stream << t;
    return *this;
  }
};

class Errors {
  llvm::SmallVector<std::unique_ptr<ErrorBuilder>> m_errors;

  Errors() {}

  friend Errors &errors();

public:
  using error_fun = llvm::function_ref<void(const Error &, size_t)>;

  ErrorBuilder &newError(clang::SourceRange range, const clang::SourceManager &SM);

  size_t size() const { return m_errors.size(); }

  void forEach(error_fun fun);
};

Errors &errors();

} // namespace vf
