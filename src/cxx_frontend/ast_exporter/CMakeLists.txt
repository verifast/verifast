cmake_minimum_required(VERSION 3.4.3)
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
  Context.cpp
  Annotation.cpp
  CommentProcessor.cpp
  ContextFreePPCallbacks.cpp
)

if(NOT MSVC)
  find_package(LLVM REQUIRED CONFIG)
  find_package(Clang REQUIRED CONFIG)

  add_definitions(${LLVM_DEFINITIONS})

  message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
  message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

  include_directories(${LLVM_INCLUDE_DIRS})
  include_directories(${CLANG_INCLUDE_DIRS})

  set(LLVM_LINK_LLVM_DYLIB OFF)

  if(NOT LLVM_ENABLE_RTTI)
    target_compile_options(vf-cxx-ast-exporter PRIVATE -fno-rtti)
  endif()

  set(LLVM_LINK_COMPONENTS
    support
  )
endif()

if(MSVC)
  set(CLANG_LIBS clangAST clangBasic clangFrontend clangTooling clangParse clangDriver clangSerialization clangSema clangEdit clangAnalysis clangASTMatchers clangFormat clangToolingInclusions clangToolingCore clangRewrite clangLex)
  set(LLVM_LIBS LLVMOption LLVMFrontendOpenMP LLVMTransformUtils LLVMAnalysis LLVMProfileData LLVMObject LLVMBitReader LLVMMCParser LLVMTextAPI LLVMCore LLVMRemarks LLVMBitstreamReader LLVMMC LLVMBinaryFormat LLVMDebugInfoCodeView LLVMDebugInfoMSF LLVMSupport LLVMDemangle)
else()
  set(CLANG_LIBS_NOMSVC clangAST clangBasic clangFrontend clangTooling)
endif()
set(CAPNP_LIBS capnp)
set(KJ_LIBS kj)

set(LIBS_PATHS "")
foreach(LIB IN LISTS CLANG_LIBS LLVM_LIBS CAPNP_LIBS KJ_LIBS)
  set(_LIB_VAR "LIB_${LIB}")
  find_library(${_LIB_VAR} NAMES lib${LIB}.a ${LIB}.lib PATHS "${VFDEPS}/lib" REQUIRED NO_CACHE)
  message(STATUS "Found lib file: ${${_LIB_VAR}}")
  list(APPEND LIBS_PATHS ${${_LIB_VAR}})
endforeach()

target_compile_options(vf-cxx-ast-exporter PRIVATE -std=c++14)

target_include_directories(vf-cxx-ast-exporter
  PRIVATE
  ${VFDEPS}/include
  "../stubs"
)

target_link_libraries(vf-cxx-ast-exporter
  PRIVATE
  ${LIBS_PATHS}
  ${CLANG_LIBS_NOMSVC}
  $<$<CXX_COMPILER_ID:MSVC>:version.lib>  
)

include(CheckCXXCompilerFlag)
check_cxx_compiler_flag("-fvisibility-inlines-hidden" SUPPORT_FVIS_INLINES_HIDDEN)
if (${SUPPORT_FVIS_INLINES_HIDDEN})
  target_compile_options(vf-cxx-ast-exporter PRIVATE -fvisibility-inlines-hidden)
endif()