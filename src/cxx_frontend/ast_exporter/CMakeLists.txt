cmake_minimum_required(VERSION 3.15)
project(VF_AST_Exporter)

set(LLVM_INSTALL_DIR "" CACHE PATH "LLVM installation directory")
set(VFDEPS "" CACHE PATH "vfdeps package directory")
set(LLVM_DIR "${LLVM_INSTALL_DIR}/lib/cmake/llvm")
set(Clang_DIR "${LLVM_INSTALL_DIR}/lib/cmake/clang")
set(CapnProto_DIR "${VFDEPS}/lib/cmake/CapnProto")

find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)
find_package(CapnProto REQUIRED CONFIG)

add_definitions(${LLVM_DEFINITIONS})

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "Using CapnProtoConfig.cmake in: ${CapnProto_DIR}")

set(PROJECT_DIR "${CMAKE_CURRENT_SOURCE_DIR}")
get_filename_component(PARENT_DIR ${PROJECT_DIR} DIRECTORY)

set(STUBS_DIR "${PARENT_DIR}/stubs")
set(STUBS_SCHEMA_NAME stubs_ast.capnp)
set(STUBS_SCHEMA "${STUBS_DIR}/${STUBS_SCHEMA_NAME}")

# The cap'n Proto tool expects windows native paths instead of cygwin paths
# These variables are converted to native paths on windows if cygpath is available
set(CAPNP_INCLUDES "${CAPNP_INCLUDE_DIRECTORY}")
set(CAPNP_STUBS_SCHEMA "${STUBS_SCHEMA}")

if(WIN32)
  find_program(CYGPATH_EXE cygpath)

  if(CYGPATH_EXE)
    function(CYGPATH TARGET)
      execute_process(COMMAND cygpath -w "${${TARGET}}" OUTPUT_VARIABLE NATIVE_PATH OUTPUT_STRIP_TRAILING_WHITESPACE)
      set(${TARGET} "${NATIVE_PATH}" PARENT_SCOPE)
    endfunction()

    cygpath(CAPNP_INCLUDES)
    cygpath(CAPNP_STUBS_SCHEMA)
  endif()
endif()

# generate stubs
add_custom_command(
  OUTPUT "${STUBS_SCHEMA}.c++" "{STUBS_SCHEMA}.h"
  WORKING_DIRECTORY "${STUBS_DIR}"
  COMMAND capnp
  ARGS
  compile
  -I "${CAPNP_INCLUDES}"
  -o "c++"
  "${STUBS_SCHEMA_NAME}"
  DEPENDS "${STUBS_SCHEMA}"
  COMMENT "Compiling Cap'n Proto schema ${STUBS_SCHEMA}"
  VERBATIM
)

add_executable(vf-cxx-ast-exporter
  Location.cpp
  VerifastASTExporter.cpp
  DeclSerializer.cpp
  StmtSerializer.cpp
  ExprSerializer.cpp
  TypeSerializer.cpp
  LocationSerializer.cpp
  ASTSerializer.cpp
  DiagnosticSerializer.cpp
  AnnotationManager.cpp
  CommentProcessor.cpp
  TranslationUnitSerializer.cpp
  FixedWidthInt.cpp
  Inclusion.cpp
  InclusionContext.cpp
  InclusionSerializer.cpp
  ContextFreePPCallbacks.cpp
  ${STUBS_SCHEMA}.c++
)

target_include_directories(vf-cxx-ast-exporter
  PRIVATE
  ${LLVM_INCLUDE_DIRS}
  ${CLANG_INCLUDE_DIRS}
  ${STUBS_DIR}
)

if(NOT LLVM_ENABLE_RTTI)
  target_compile_options(vf-cxx-ast-exporter PRIVATE -fno-rtti)
endif()

llvm_map_components_to_libnames(LLVM_LIBS)
set(CLANG_LIBS clangTooling)

set_property(TARGET vf-cxx-ast-exporter PROPERTY CXX_STANDARD 20)

target_link_libraries(vf-cxx-ast-exporter
  PRIVATE
  ${LLVM_LIBS}
  ${CLANG_LIBS}
  CapnProto::capnp
)

include(CheckCXXCompilerFlag)
check_cxx_compiler_flag("-fvisibility-inlines-hidden" SUPPORT_FVIS_INLINES_HIDDEN)

if(${SUPPORT_FVIS_INLINES_HIDDEN})
  target_compile_options(vf-cxx-ast-exporter PRIVATE -fvisibility-inlines-hidden)
endif()