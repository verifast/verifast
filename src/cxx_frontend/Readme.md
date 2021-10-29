
# Cxx Frontend

VeriFast's Cxx Frontend adds support to verify simple C++ programs. The frontend translates a C++ abstract syntax tree (AST) to an AST that VeriFast is able to process, in order to verify the program.

## Compiling from source
The usual guidelines ([Windows](../../Readme.windows.md), [Linux](../../Readme.Linux.md), [MacOS](../../Readme.MacOS.md)) hold in order to be able to compile VeriFast from source with C++ support. In addition, it is also required to have an `LLVM` and `Clang` installation (or its source code) and setup `CMake` in order to compile the [cxx-ast-exporter tool](###Cxx-Ast-Exporter).

### Unix
No additional steps are required. The [setup-build.sh](../../setup-build.sh) script installs pre-compiled `LLVM/Clang 13` binaries and `CMake`. Follow the compilation instructions for [Linux](../../Readme.Linux.md) or [MacOS](../../Readme.MacOS.md).

### Windows
`LLVM` and `Clang` have to be compiled from source on Windows. This requires an installation of [Visual Studio](https://visualstudio.microsoft.com/) with C++ support and `CMake`. Check the [Windows compilation instructions](../../Readme.Windows.md) for more details. 

## Outline
### Cxx Frontend Signature
The [frontend signature](cxx_fe_sig.ml) provides two module types related to the frontend:
- `Cxx_Ast_Translator`: defines the interface of the module that translates C++ ASTs to ASTs that VeriFast can process. It exposes the function `parse_cxx_file` to translate an AST and is the entry point of the frontend.
- `CXX_TRANSLATOR_ARGS`: defines the arguments that should be passed to the `Cxx_Ast_Translator` module.

### Cxx AST Translator
[This module](cxx_ast_translator.ml) implements the `Cxx_AST_Translator` interface. It defines *translate* functions for each node that can appear in the C++ AST. Using these functions, the translator recursively traverses each node in the AST and maps it to nodes that VeriFast can use. This results in an AST that VeriFast can process.

### Cxx Annotation Parser
VeriFast annotations that appear in a C++ AST are included as raw text. The [annotation parser](cxx_annotation_parser.ml) defines functions to parse those annotations. The AST translator invokes the annotation parser when it encounters an annotation. This produces a sub-AST which represents the annotation, and is included in the main AST.

### Cxx-Ast-Exporter
In order to produce a C++ AST and export it to VeriFast afterwards, a tool has been written using LLVM's [LibTooling library](https://clang.llvm.org/docs/LibTooling.html). More information can be found [here](ast_exporter/Readme.md).

### Stubs
[Cap'n proto](https://capnproto.org/) is used to (de)serialize the C++ AST and transmit it to VeriFast's C++ frontend. Stubs code is auto generated for OCaml and C++ in order to (de)serialize from C++ to OCaml. This auto-generated code uses a [stubs schema](stubs/stubs_ast.capnp) which represents the different structures that can be (de)serialized. The stubs schema defines simplified C++ AST nodes.