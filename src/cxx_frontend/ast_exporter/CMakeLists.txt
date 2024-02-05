cmake_minimum_required(VERSION 3.15)
project(VF_AST_Exporter)

set(LLVM_INSTALL_DIR "" CACHE PATH "LLVM installation directory")
set(VFDEPS "" CACHE PATH "vfdeps package directory")
set(LLVM_DIR "${LLVM_INSTALL_DIR}/lib/cmake/llvm")
set(Clang_DIR "${LLVM_INSTALL_DIR}/lib/cmake/clang")

add_executable(vf-cxx-ast-exporter
  VerifastASTExporter.cpp
  DeclSerializer.cpp
  StmtSerializer.cpp
  ExprSerializer.cpp
  TypeSerializer.cpp
  AstSerializer.cpp
  InclusionContext.cpp
  Annotation.cpp
  CommentProcessor.cpp
  ContextFreePPCallbacks.cpp
  Location.cpp
  FixedWidthInt.cpp
  AnnotationStore.cpp
  Inclusion.cpp
)

find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

add_definitions(${LLVM_DEFINITIONS})

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

target_include_directories(vf-cxx-ast-exporter
  PRIVATE
  ${LLVM_INCLUDE_DIRS}
  ${CLANG_INCLUDE_DIRS}
)

if(NOT LLVM_ENABLE_RTTI)
  target_compile_options(vf-cxx-ast-exporter PRIVATE -fno-rtti)
endif()

llvm_map_components_to_libnames(LLVM_LIBS support)
set(CLANG_LIBS clangAST clangBasic clangFrontend clangTooling)
set(CAPNP_LIBS capnp)
set(KJ_LIBS kj)

set(LIBS_PATHS "")

foreach(LIB IN LISTS CAPNP_LIBS KJ_LIBS)
  set(_LIB_VAR "LIB_${LIB}")
  find_library(${_LIB_VAR} NAMES lib${LIB}.a ${LIB}.lib PATHS "${VFDEPS}/lib" REQUIRED NO_CACHE NO_DEFAULT_PATH)
  message(STATUS "Found lib file: ${${_LIB_VAR}}")
  list(APPEND LIBS_PATHS ${${_LIB_VAR}})
endforeach()

set_property(TARGET vf-cxx-ast-exporter PROPERTY CXX_STANDARD 20)

target_include_directories(vf-cxx-ast-exporter
  PRIVATE
  ${VFDEPS}/include
  "../stubs"
)

target_link_libraries(vf-cxx-ast-exporter
  PRIVATE
  ${LIBS_PATHS}
  ${LLVM_LIBS}
  ${CLANG_LIBS}
)

include(CheckCXXCompilerFlag)
check_cxx_compiler_flag("-fvisibility-inlines-hidden" SUPPORT_FVIS_INLINES_HIDDEN)

if(${SUPPORT_FVIS_INLINES_HIDDEN})
  target_compile_options(vf-cxx-ast-exporter PRIVATE -fvisibility-inlines-hidden)
endif()