#pragma once
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Mangle.h"
#include <unordered_map>

namespace vf {
class FunctionMangler {
  std::unique_ptr<clang::MangleContext> m_mangler;

  std::unordered_map<int64_t, std::string> m_mangledNames;

  llvm::StringRef getMangledName(const clang::NamedDecl *nd,
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

public:
  explicit FunctionMangler(clang::ASTContext &context)
      : m_mangler(clang::ItaniumMangleContext::create(
            context, context.getDiagnostics())){};

  llvm::StringRef mangleFunc(const clang::FunctionDecl *decl) {
    clang::GlobalDecl gd(decl);
    return getMangledName(decl, gd);
  }

  llvm::StringRef mangleCtor(const clang::CXXConstructorDecl *decl) {
    clang::GlobalDecl gd(decl, clang::Ctor_Complete);
    return getMangledName(decl, gd);
  }

  llvm::StringRef mangleDtor(const clang::CXXDestructorDecl *decl) {
    clang::GlobalDecl gd(decl, clang::Dtor_Complete);
    return getMangledName(decl, gd);
  }
};
} // namespace vf