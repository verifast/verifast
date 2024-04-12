#pragma once

#if __cpp_concepts >= 201907
#include "stubs_ast.capnp.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include "clang/AST/TypeLoc.h"
#include <concepts>

template <typename T, typename... U>
concept IsAnyOf = (std::same_as<T, U> || ...);

template <typename T>
concept IsStubsNode =
    IsAnyOf<T, stubs::Decl, stubs::Stmt, stubs::Expr, stubs::Type>;

template <typename T>
concept IsAstNode = IsAnyOf<T, clang::Decl, clang::Stmt, clang::Expr,
                            clang::Type, clang::TypeLoc>;

template <typename T>
concept IsLoopAstNode = IsAnyOf<T, clang::WhileStmt, clang::DoStmt, clang::ForStmt>;

#else
#define IsAnyOf typename
#define IsStubsNode typename
#define IsAstNode typename
#define IsLoopAstNode typename
#endif