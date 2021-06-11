# LibTooling C++ AST Exporter
The C++ AST Exporter is a standalone tool writtin with [LLVM's LibTooling library](https://clang.llvm.org/docs/LibTooling.html). This tool main purpose is to traverse the C++ Abstract Syntax Tree (AST) and export it to VeriFast's C++ frontend. In addition, it checks if all macro expansions are context-free. This means that the definition of a macro [cannot depend on the context it is included in](https://people.cs.kuleuven.be/~bart.jacobs/verifast/symbolicpp.pdf).

## Compiling
To be able to compile this tool, it is required to either have an installation of LLVM and Clang, or have its source code. Currently, versions 10.0.x - 11.1.x have been tested and can be used to compile the tool. Follow the instructions listed below to install LLVM and Clang and setup CMake for the build process.

### Obtaining LLVM and Clang
There are several ways to obtain LLVM and Clang:
- Download the binaries from the [release page](https://github.com/llvm/llvm-project/releases) and extract it to a folder of choice afterwards. Make sure to dowload `clang+llvm-*version*-*architecture*-*platform*.tar.xz` and not only LLVM or Clang or the source code. Be aware that binaries are not always available for each platform and all versions. This is probably the preferred, fastest and easiest way.
- Use your package manager to install:
    - E.g. Homebrew on MacOS: `brew install llvm@11`
    - E.g. Apt on Linux: `apt-get install llvm-11 clang-11`
- Compile from source: 
    **this can take a long time**
    1. Download its [source code](https://github.com/llvm/llvm-project/tree/main) and extract it. Make sure to select the branch that matches the version you want to download. 
    2. Create a *build* directory at you preferred location: `mkdir build`. Be aware LLVM cannot be build in its source directory. Afterwards `cd` to this directory: `cd build`.
    3. Setup Cmake: `cmake path/to/llvm/source/root`.
    4. Build the components that are required for the tool: 
        ```
        make clang clangAST clangBasic clangFrontend clangTooling
        ```

### Setup CMake
Now use CMake te create an automated build process:
1. `cd` to the AST exporter tool's build directory:    
    ```
    cd /path/to/verifast/source/src/cxx_frontend/libtooling/build
    ```
2. Instruct CMake where it can find your LLVM installation and your vfdeps package:
    ```
    cmake -DLLVM_INSTALL_DIR=path/to/llvm -DVFDEPS=/path/to/vfdeps -DCMAKE_BUILD_TYPE=Release ..
    ```

    The build type is optional and can be one of `Release`, `Debug`, `RelWithDebInfo` and `MinSizeRel`.

Now you can simply run `make` from VeriFast's `src` folder like usual.

## Outline
This section lists most important components of the C++ AST Exporter tool:
- [VerifastASTExporter](VerifastASTExporter.cpp): the entry point of the tool. It creates a frontend action that will process the given source file.
- [NodeSerializer](NodeSerializer.h): declares visitors for C++ AST nodes. Those are used to traverse declarations, statements, expressions and types, and serialize them.
- [DeclSerializer](DeclSerializer.cpp), [StmtSerializer](StmtSerializer.cpp), [ExprSerializer](ExprSerializer.cpp), [TypeSerializer](TypeSerializer.cpp): define the visitors declared in [NodeSerializer](NodeSerializer.h).
- [AstSerializer](AstSerializer.h): entry point to serialize any AST node. It delegates the serialization to a specific serializer for that node.
- [AnnotationStore](AnnotationStore.h): container that holds VeriFast annotations encountered during preprocessing. It also exposes methods to query them.
- [CommentProcessor](CommentProcessor.h): processes every comment encountered during preprocessing and ads it to the [AnnotationStore](AnnotationStore.h) if it appears to be a VeriFast annotation.
- [ContextFreePPCallbacks](ContextFreePPCallbacks.h): callbacks that are used during preprocessing. These callabcks check if macro expansions are context-free.