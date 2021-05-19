#pragma once
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Mangle.h"
#include <unordered_map>

namespace vf {
class FunctionMangler {
  std::unique_ptr<clang::MangleContext> _mangler;

  std::unordered_map<int64_t, std::string> _mangledNames;

  llvm::StringRef getMangledName(const clang::NamedDecl *nd, const clang::GlobalDecl &gd) {
    auto id = nd->getID();
    auto search = _mangledNames.find(id);
    if (search != _mangledNames.end()) {
      return search->second;
    }
    if (_mangler->shouldMangleDeclName(nd)) {
      std::string name;
      {
        llvm::raw_string_ostream os(name);
        _mangler->mangleName(gd, os);
      }
      _mangledNames.emplace(id, std::move(name));
    } else {
      _mangledNames.emplace(id, nd->getNameAsString());
    }
    return _mangledNames[id];
  }

public:
  explicit FunctionMangler(clang::ASTContext &context)
      : _mangler(clang::ItaniumMangleContext::create(
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