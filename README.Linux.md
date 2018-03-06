Building VeriFast on Linux
==========================

Note: binary downloads are available, both ["nightly" builds](https://github.com/verifast/verifast#binaries) of the latest commit, and binaries for [named releases](https://github.com/verifast/verifast/releases).

Note: The instructions below may get out of date. When that happens, please submit an issue. In the meantime, guaranteed up-to-date instructions can be found by looking at the script, [.travis.yml](https://github.com/verifast/verifast/blob/master/.travis.yml), used by the Travis CI service that automatically builds and tests VeriFast after each commit. This script, which runs on a Ubuntu 14.04 (Trusty) virtual machine, first runs the command listed below `install:`, and then the command listed below `script:`.

Dependencies
------------

To install the software needed to build VeriFast, run [setup-build.sh](https://github.com/verifast/verifast/blob/master/setup-build.sh). This script does the following:

- It installs some non-OCaml-based dependencies using `apt-get`:
    ```
    sudo apt-get install -y --no-install-recommends \
         git wget ca-certificates make m4 \
         gcc patch unzip libgtk2.0-dev \
         valac gtksourceview2.0-dev
    ```
- It installs the OCaml-based dependencies:
  - OCaml 4.06.0
  - Findlib 1.7.3 (for the `ocamlfind` tool, used by Z3's install script)
  - OCaml-Num (arbitrary-precision arithmetic)
  - Ocamlbuild (to build Camlp4)
  - Camlp4 (an OCaml preprocessor, for the streams notation used in VeriFast's parser)
  - Lablgtk (OCaml bindings to the GTK+ GUI toolkit)
  - Z3 4.5.0 (a powerful theorem prover, including OCaml bindings)
  
  It does so by downloading a [VFDeps](http://people.cs.kuleuven.be/~bart.jacobs/verifast/vfdeps-ocaml-4.06.0-trusty.tar.xz) package from my (Bart Jacobs') homepage with pre-compiled versions of these dependencies. I created this package by running the [make_vfdeps/Makefile.deps](https://github.com/verifast/verifast/blob/master/make_vfdeps/Makefile.deps) Makefile using GNU make. Note: these binaries are location-dependent. They need to be below `/tmp/vfdeps`; that is, extract the archive into `/tmp`. (You can also extract it elsewhere and then create a symlink called `/tmp/vfdeps` that points there.)

Building VeriFast
-----------------

To build VeriFast:
1. `cd src`
2. Make sure all dependencies are in your `PATH`. For example: `export PATH=/tmp/vfdeps/bin:$PATH`.
3. `make`
