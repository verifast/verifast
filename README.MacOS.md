Building VeriFast on macOS
==========================

Note: binary downloads are available, both ["nightly" builds](https://github.com/verifast/verifast#binaries) of the latest commit, and binaries for [named releases](https://github.com/verifast/verifast/releases).

Note: The instructions below may get out of date. When that happens, please submit an issue. In the meantime, guaranteed up-to-date instructions can be found by looking at the script, [.github/workflows/build.yml](https://github.com/verifast/verifast/blob/master/.github/workflows/build.yml), used by the Github Actions CI service that automatically builds and tests VeriFast after each commit. This script uses the `build_macos` job, which runs on a MacOS Catalina (10.15) virtual machine. It first runs the command listed below `Build setup:`, and then the command listed below `Build:`.

Dependencies
------------

To install the software needed to build VeriFast, first install Xcode (at least the command-line tools) and Homebrew. Then run [setup-build.sh](https://github.com/verifast/verifast/blob/master/setup-build.sh). This script does the following:

- It installs the `wget`, `gtk+`, `gtksourceview`, `vala`, and `cmake` packages using `brew install`.
- It installs LLVM/Clang 13.0.0 (a language front-end and tooling infrastructure for languages in the C language family).
- It installs the OCaml-based dependencies:
  - OCaml 4.13.0
  - Findlib 1.9.1 (for the `ocamlfind` tool, used by Z3's install script and dune)
  - OCaml-Num 1.4 (arbitrary-precision arithmetic)
  - Ocamlbuild 0.14.0 (to build Camlp4)
  - Camlp4 4.13+1 (an OCaml preprocessor, for the streams notation used in VeriFast's parser)
  - GTK+ (a cross-platform GUI toolkit)
  - Lablgtk 2.18.11 (OCaml bindings to GTK+)
  - Z3 4.8.5 (a powerful theorem prover, including OCaml bindings)
  - Dune 2.9.1 (to build and install other OCaml dependencies)
  - Cap'n Proto 0.9.1 (fast data interchange format)
  - Capnp 3.4.0 (OCaml plugin for Cap'n Proto)
  - Other dependencies, mainly to support Capnp:
    - Csexp 1.5.1
    - Sexplib0 0.14.0
    - Base 0.14.1
    - Res 5.0.1
    - Stdio 0.14.0
    - Cppo 1.6.8
    - Ocplib-endian 1.1
    - Stdint 0.7.0
    - Result 1.5
  
It does so by downloading a [vf-llvm-clang-build](https://github.com/NielsMommen/vf-llvm-clang-build/releases/tag/v1.0.0) and [VFDeps](https://github.com/verifast/vfdeps) package with pre-compiled versions of these dependencies. Note: these binaries are location-dependent. They need to be below `/usr/local/vf-llvm-clang-build-$VERSION` and `/usr/local/vfdeps-$VERSION`, where `$VERSION` is the version (Git hash) of the package; that is, extract the archives into `/usr/local`. To see which version is currently being used, see [config.sh](https://github.com/verifast/verifast/blob/master/config.sh).

Building VeriFast
-----------------

To build VeriFast:
1. `cd src`
2. Make sure all dependencies are in your `PATH`. For example: `export PATH=/usr/local/vfdeps-$VERSION/bin:$PATH`.
3. Make sure the dependencies' DLLs can be found by the macOS DLL loader. For example: `export DYLD_LIBRARY_PATH=/usr/local/vfdeps-$VERSION/lib:$DYLD_LIBRARY_PATH`.
4. `make`