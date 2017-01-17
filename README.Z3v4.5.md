Building VeriFast against Z3 version 4.5
========================================

Tested on OS X.

We will build Z3, including the Z3 OCaml API, from the sources found on https://github.com/Z3Prover/z3. However, Z3's build script uses `ocamlfind`. Therefore, we first need to install `ocamlfind`. To do so, we install `opam`. So:

- Install opam (`brew install opam; opam init`)
- Install ocamlfind (`opam install ocamlfind`)
- Download the Z3 source code from https://github.com/Z3Prover/z3
- Build and install Z3 using the instructions from the README:
  
        python scripts/mk_make.py --ml
        cd build
        make
        sudo make install
  
  We now have the Z3 OCaml modules in the directory printed by `ocamlfind query z3`, and we have the Z3 DLL (`libz3.dylib`) in `/usr/local/lib`.
- Build VeriFast with Z3v4.5 support: in the VeriFast directory: `cd src; make Z3V4DOT5=yes`.
- Even if VeriFast is built with Z3v4.5 support, Redux is the default prover. To use Z3, write `vfide -prover z3v4.5`.
