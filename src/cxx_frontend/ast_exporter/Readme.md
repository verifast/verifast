# LibTooling C++ AST Exporter
The C++ AST Exporter is a standalone tool written with [LLVM's LibTooling library](https://clang.llvm.org/docs/LibTooling.html). This tool's main purpose is to traverse the C++ Abstract Syntax Tree (AST) and export it to VeriFast's C++ frontend. In addition, it checks if all macro expansions are context-free. This means that the definition of a macro [cannot depend on the context it is included in](https://people.cs.kuleuven.be/~bart.jacobs/verifast/symbolicpp.pdf).

## Compiling
To be able to compile this tool, it is required to either have an installation of LLVM and Clang, or have its source code. Currently, version 13.x.x can be used to compile the tool.

### Unix
[setup-build.sh](../../../setup-build.sh) installs the required llvm/clang components and sets up CMake for the build process.

### Windows
The [vfdeps package](https://github.com/NielsMommen/vfdeps-win) for windows contains the required pre-compiled llvm/clang libraries and header files. In order to compile the C++ AST Exporter, it is required to have a [Visual Studio](https://visualstudio.microsoft.com/) (community) installation with support for C++ desktop development.

Open a Cygwin terminal and add the directory where `vcvarsall.bat` is located to your path: 
```
export PATH=/cygdrive/c/path-to-visual-studio-installation/2019/Community/VC/Auxiliary/Build:$PATH
```
This allows VeriFast to use the C++ toolchain from the command line. [setup-windows.sh](../../../setup-windows.sh) sets up CMake for the build process.

### Compilation
Now you can simply run `make` from VeriFast's `src` folder like usual, or use `make build-cxx-libtool` to only compile the C++ AST exporter tool.

## Outline
This section lists most important components of the C++ AST Exporter tool:
- [VerifastASTExporter](VerifastASTExporter.cpp): the entry point of the tool. It creates a frontend action that will process the given source file.
- [NodeSerializer](NodeSerializer.h): declares visitors for C++ AST nodes. These are used to traverse declarations, statements, expressions, annotations and types, and serialize them.
- [DeclSerializer](DeclSerializer.cpp), [StmtSerializer](StmtSerializer.cpp), [ExprSerializer](ExprSerializer.cpp), [TypeSerializer](TypeSerializer.cpp): define the visitors declared in [NodeSerializer](NodeSerializer.h).
- [AstSerializer](AstSerializer.h): entry point to serialize any AST node. It delegates the serialization to a specific serializer for that node.
- [AnnotationStore](AnnotationStore.h): container that holds VeriFast annotations encountered during preprocessing. It also exposes methods to query them.
- [CommentProcessor](CommentProcessor.h): processes every comment encountered during preprocessing and ads it to the [AnnotationStore](AnnotationStore.h) if it appears to be a VeriFast annotation.
- [ContextFreePPCallbacks](ContextFreePPCallbacks.h): callbacks that are used during preprocessing. These callbacks check if macro expansions are context-free.