# LibTooling C++ AST Exporter
The C++ AST Exporter is a standalone tool written with [LLVM's LibTooling library](https://clang.llvm.org/docs/LibTooling.html). This tool's main purpose is to traverse the C++ Abstract Syntax Tree (AST) and export it to VeriFast's C++ frontend. In addition, it checks if all macro expansions are context-free. This means that the definition of a macro [cannot depend on the context it is included in](https://people.cs.kuleuven.be/~bart.jacobs/verifast/symbolicpp.pdf).

## Compiling
To be able to compile this tool, it is required to either have an installation of LLVM and Clang, or have its source code. Currently, version 13.x.x can be used to compile the tool.

[setup-build.sh](../../../setup-build.sh)/[setup-windows.sh](../../../setup-windows.sh) installs the required llvm/clang pre-compiled components for your platform and sets up CMake for the build process.

### Compilation
Now you can simply run `make` from VeriFast's `src` folder like usual, or use `make build-cxx-libtool` to only compile the C++ AST exporter tool.

## Outline
This section lists most important components of the C++ AST Exporter tool:
- [VerifastASTExporter](VerifastASTExporter.cpp): the entry point of the tool. It creates a frontend action that will process the given source file.
- [Serializer](Serializer.h): defines interfaces for serializer (of AST nodes). Implementations of serializers derives from these interfaces.
- [DeclSerializer](DeclSerializer.cpp), [StmtSerializer](StmtSerializer.cpp), [ExprSerializer](ExprSerializer.cpp), [TypeSerializer](TypeSerializer.cpp): define serializers for their corresponding clang AST nodes.
- [AstSerializer](AstSerializer.h): entry point to serialize any AST node. It delegates the serialization to a specific serializer for that node.
- [AnnotationManager](AnnotationManager.h): container that holds VeriFast annotations encountered during preprocessing. It also exposes methods to query them.
- [CommentProcessor](CommentProcessor.h): processes every comment encountered during preprocessing and ads it to the [AnnotationManager](AnnotationManager.h) if it appears to be a VeriFast annotation.
- [ContextFreePPCallbacks](ContextFreePPCallbacks.h): callbacks that are used during preprocessing. These callbacks check if macro expansions are context-free.