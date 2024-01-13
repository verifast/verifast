
# Cxx Frontend

VeriFast's Cxx Frontend adds support to verify simple C++ programs. The frontend translates a C++ abstract syntax tree (AST) to an AST that VeriFast is able to process, in order to verify the program.

## Compiling from source
The usual guidelines ([Windows](../../Readme.windows.md), [Linux](../../Readme.Linux.md), [MacOS](../../Readme.MacOS.md)) hold in order to be able to compile VeriFast from source with C++ support.

## Outline
### Frontend Signature
The [frontend signature](sig.ml) provides two module types related to the frontend:
- `Cxx_Ast_Translator`: defines the interface of the module that translates C++ ASTs to ASTs that VeriFast can process. It exposes the function `parse_cxx_file` to translate an AST and is the entry point of the frontend.
- `CXX_TRANSLATOR_ARGS`: defines the arguments that should be passed to the `Ast_Translator` module.

### AST Translator
[This module](ast_translator.ml) implements the `Cxx_AST_Translator` interface. It allows to translate a translation unit to VeriFast packages.

### Node Translator
The [node translator](node_translator.ml) exposes entry functions in order to translate C++ AST nodes. Following modules are functors that have to be instantiated with this translator in order to translate specific AST nodes:
* [Decl Translator](decl_translator.ml): translation of declarations
* [Stmt Translator](stmt_translator.ml): translation of statements
* [Expr Translator](expr_translator.ml): translation of expressions
* [Type Translator](type_translator.ml): translation of types
* [Var Translator](var_translator.ml): translations of variable declarations

### Annotation Parser
VeriFast annotations that appear in a C++ AST are included as raw text. The [annotation parser](cxx_annotation_parser.ml) defines functions to parse those annotations. The AST translator invokes the annotation parser when it encounters an annotation. This produces a sub-AST which represents the annotation, and is included in the main AST.

### Cxx-Ast-Exporter
In order to produce a C++ AST and export it to VeriFast afterwards, a tool has been written using LLVM's [LibTooling library](https://clang.llvm.org/docs/LibTooling.html). More information can be found [here](ast_exporter/Readme.md).

### Stubs
[Cap'n proto](https://capnproto.org/) is used to (de)serialize the C++ AST and transmit it to VeriFast's C++ frontend. Stubs code is auto generated for OCaml and C++ in order to (de)serialize from C++ to OCaml. This auto-generated code uses a [stubs schema](stubs/stubs_ast.capnp) which represents the different structures that can be (de)serialized. The stubs schema defines simplified C++ AST nodes.