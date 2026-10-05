
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

## Function templates
A function template whose body only uses its type parameters in ways that mean the same for every scalar type is verified once, not once per instantiation. The exporter serializes the template itself, including its dependent body. The translator turns it into a single generic function, such as `identity<T>(const T)`, whose template type parameters are ghost type parameters (`GhostTypeParam`). Such a template is verified even if nothing instantiates it.

A call to a specialization of such a template whose type arguments are all scalar types (arithmetic types, `bool`, enumerations or pointers) is a call of the generic function, with the type arguments Clang deduced. The generic proof models copying and destroying a value of a type parameter as plain value operations, which is exact only for these types. A specialization with any other type argument, such as a class type, is translated and verified separately. Its copy constructors and destructors are then checked against their contracts.

Every other function template is verified separately for each of its specializations, and not at all if nothing instantiates it. This is the case if the template:
- uses members of a type parameter (`t->m_x`),
- makes calls whose arguments depend on a type parameter (including calls of other templates),
- applies operators other than `=`, `*` and `&` to type-dependent operands,
- converts to or from a type parameter implicitly (for instance, `int f(T x) { return x; }`), or uses a type-dependent condition,
- uses casts, `sizeof`, indexing or `new`/`delete` that depend on a type parameter,
- initializes a type-dependent variable other than with `=`, or uses types other than type parameters and pointers and lvalue references to them,
- has non-type, template template or variadic template parameters, or is a member function template.

The exporter decides this from the C++ code only, because annotations reach it as raw text. A template whose contract or ghost code only type-checks for particular type arguments (for instance, `requires x > 0`) therefore gets a generic function that fails. VeriFast then verifies the program again, with that template verified per specialization, exactly as if its C++ body could not be verified generically:
- If the generic function does not type-check, the template is verified per specialization, and not at all if nothing instantiates it.
- If the generic function type-checks but does not verify, the template is verified per specialization if something instantiates it. Otherwise, the verification failure is reported.

The verifier attributes an error to a template if it occurs while checking the header or verifying the body of its generic function, and `verify_program` (`src/verifast.ml`) passes the names of the generic functions that failed to the exporter (`-generic_fallback` and `-generic_fallback_if_instantiated`). With `-verbose 1`, VeriFast reports each template that it verifies per specialization this way.

