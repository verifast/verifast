cmake_minimum_required(VERSION 3.4.3)
project(VF_AST_Exporter)

set(LLVM_INSTALL_DIR "" CACHE PATH "LLVM installation directory")
set(VFDEPS "" CACHE PATH "vfdeps package directory")

set(LLVM_DIR "${LLVM_INSTALL_DIR}/lib/cmake/llvm")
set(Clang_DIR "${LLVM_INSTALL_DIR}/lib/cmake/clang")

find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

add_definitions(${LLVM_DEFINITIONS})

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "Using vfdeps package: ${VFDEPS}")

include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${CLANG_INCLUDE_DIRS})

find_library(CAPNP_LIB NAMES libcapnp.a capnp PATHS "${VFDEPS}/lib" REQUIRED)
find_library(KJ_LIB NAMES libkj.a kj PATHS "${VFDEPS}/lib" REQUIRED)

message(STATUS "Found capnp lib: ${CAPNP_LIB}")
message(STATUS "Found kj lib: ${KJ_LIB}")

set(LLVM_LINK_LLVM_DYLIB OFF)
set(CMAKE_CXX_STANDARD 14 CACHE STRING "")

if(NOT LLVM_ENABLE_RTTI)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
endif()

set(LLVM_LINK_COMPONENTS
  support
  )

add_executable(vf-cxx-ast-exporter
  VerifastASTExporter.cpp
  DeclSerializer.cpp
  StmtSerializer.cpp
  ExprSerializer.cpp
  TypeSerializer.cpp
  AstSerializer.cpp
  Context.cpp
  Annotation.cpp
  CommentProcessor.cpp
  ContextFreePPCallbacks.cpp
)

target_include_directories(vf-cxx-ast-exporter
  PRIVATE
  ${VFDEPS}/include
  "../stubs"
)

set(CLANG_LIBS clangAST clangBasic clangFrontend clangTooling)

target_link_libraries(vf-cxx-ast-exporter
  PRIVATE
  ${CAPNP_LIB}
  ${KJ_LIB}
  ${CLANG_LIBS}
)

include(CheckCXXCompilerFlag)
check_cxx_compiler_flag("-fvisibility-inlines-hidden" SUPPORT_FVIS_INLINES_HIDDEN)
if (${SUPPORT_FVIS_INLINES_HIDDEN})
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fvisibility-inlines-hidden")
endif()