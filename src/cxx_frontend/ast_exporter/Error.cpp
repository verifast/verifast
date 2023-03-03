#include "Error.h"

namespace vf {

void ErrorRange::serialize(stubs::Loc::Builder &builder) const {
  if (!m_valid)
    return;
  auto startBuilder = builder.initStart();
  auto endBuilder = builder.initEnd();
  serializeSrcPos(startBuilder, m_begin);
  serializeSrcPos(endBuilder, m_end);
}

ErrorBuilder &Errors::newError(clang::SourceRange range,
                               const clang::SourceManager &SM) {
  return *m_errors.emplace_back(
      std::move(std::make_unique<ErrorBuilder>(range, SM)));
}

void Errors::forEach(error_fun fun) {
  size_t i(0);
  for (const auto &err : m_errors) {
    Error e = *err;
    fun(e, i++);
  }
}

Errors &errors() {
  static Errors errs;
  return errs;
}

} // namespace vf