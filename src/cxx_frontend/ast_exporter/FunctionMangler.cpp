#include "FunctionMangler.h"

namespace vf {
llvm::StringRef FunctionMangler::getMangledName(const clang::NamedDecl *nd,
                                                const clang::GlobalDecl &gd) {
  auto id = nd->getMostRecentDecl()->getID();
  auto search = m_mangledNames.find(id);
  if (search != m_mangledNames.end()) {
    return search->second;
  }
  if (m_mangler->shouldMangleDeclName(nd)) {
    std::string name;
    {
      llvm::raw_string_ostream os(name);
      m_mangler->mangleName(gd, os);
    }
    m_mangledNames.emplace(id, std::move(name));
  } else {
    m_mangledNames.emplace(id, nd->getNameAsString());
  }
  return m_mangledNames[id];
}
} // namespace vf