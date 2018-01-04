[![Build Status](https://travis-ci.org/verifast/verifast.svg?branch=master)](https://travis-ci.org/verifast/verifast) [![Build status](https://ci.appveyor.com/api/projects/status/1w7vchky3k6erltw?svg=true)](https://ci.appveyor.com/project/verifast/verifast) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.819853.svg)](https://doi.org/10.5281/zenodo.819853)

VeriFast
========

By Bart Jacobs\*, Jan Smans\*, and Frank Piessens\*, with contributions by Pieter Agten\*, Cedric Cuypers\*, Lieven Desmet\*, Jan Tobias Muehlberg\*, Willem Penninckx\*, Pieter Philippaerts\*, Amin Timany\*, Thomas Van Eyck\*, Gijs Vanspauwen\*,  Frédéric Vogels\*, and [external contributors](https://github.com/verifast/verifast/graphs/contributors)

\* imec-DistriNet research group, Department of Computer Science, KU Leuven - University of Leuven, Belgium

VeriFast is a research prototype of a tool for modular formal verification of correctness properties of single-threaded and multithreaded C and Java programs annotated with preconditions and postconditions written in separation logic. To express rich specifications, the programmer can define inductive datatypes, primitive recursive pure functions over these datatypes, and abstract separation logic predicates. To verify these rich specifications, the programmer can write lemma functions, i.e., functions that serve only as proofs that their precondition implies their postcondition. The verifier checks that lemma functions terminate and do not have side-effects. Since neither VeriFast itself nor the underlying SMT solver need to do any significant search, verification time is predictable and low.

The VeriFast source code and binaries are released under the [MIT license](LICENSE.md).

Binaries
--------

Within an hour after each push to the master branch, binary packages become available at the following URLs:

- [Windows](https://ci.appveyor.com/api/projects/verifast/verifast/artifacts/src/verifast-nightly.zip?branch=master)
- [Linux/x64](http://82076e0e62875f063ae8-929808a701855dfb71539d0a4342d4be.r54.cf5.rackcdn.com/verifast-nightly.tar.gz)
- [OS X](http://82076e0e62875f063ae8-929808a701855dfb71539d0a4342d4be.r54.cf5.rackcdn.com/verifast-nightly-osx.tar.gz)

These "nightly" builds are very stable and are recommended. Still, named releases are available [here](https://github.com/verifast/verifast/releases). (An archive of older named releases is [here](https://people.cs.kuleuven.be/~bart.jacobs/verifast/releases/).)

Simply extract the files from the archive to any location in your filesystem. All files in the archive are in a directory named `verifast-COMMIT` where `COMMIT` describes the Git commit. For example, on Linux:

    tar xzf ~/Downloads/verifast-nightly.tar.gz
    cd verifast-<TAB>  # Press Tab to autocomplete
    bin/vfide examples/java/termination/Stack.jarsrc  # Launch the VeriFast IDE with the specified example
    ./test.sh  # Run the test suite (verifies all examples)

Compiling
---------
- [Windows](README.Windows.md)
- [Linux](README.Linux.md)
- [OS X](README.MacOS.md)

Documentation
-------------

- [The VeriFast Tutorial](https://doi.org/10.5281/zenodo.887906)
- [Featherweight VeriFast](http://arxiv.org/pdf/1507.07697) [(Slides, handouts, Coq proof)](https://people.cs.kuleuven.be/~bart.jacobs/fvf)
- [Scientific papers](https://people.cs.kuleuven.be/~bart.jacobs/verifast/) on the various underlying ideas

Acknowledgements
----------------

### Dependencies

We gratefully acknowledge the authors and contributors of the following software packages.

#### Bits that we ship in our binary packages

- [OCaml](http://caml.inria.fr)
- [OCaml-Num](https://github.com/ocaml/num)
- [Lablgtk](http://lablgtk.forge.ocamlcore.org)
- [GTK+](https://www.gtk.org) and its dependencies (including GLib, Cairo, Pango, ATK, gdk-pixbuf, gettext, fontconfig, freetype, expat, libpng, zlib, Harfbuzz, and Graphite)
- [GtkSourceView](https://wiki.gnome.org/Projects/GtkSourceView)
- The excellent [Z3](https://github.com/Z3Prover/z3) theorem prover by Leonardo de Moura and Nikolaj Bjorner at Microsoft Research, and co-authors

#### Software used at build time

- findlib, ocamlbuild, camlp4, valac
- Cygwin, Homebrew, Debian, Ubuntu
- The usual infrastructure: GNU/Linux, GNU make, gcc, etc.

### Infrastructure

We gratefully acknowledge the following infrastructure providers.

- GitHub
- Travis CI
- AppVeyor CI

### Funding

This work is supported in part by the Flemish Research Fund (FWO-Vlaanderen), by the EU FP7 projects SecureChange, STANCE, ADVENT, and VESSEDIA, by Microsoft Research Cambridge as part of the Verified Software Initiative, and by the Research Fund KU Leuven.

Third-Party Resources
---------------------

- Kiwamu Okabe created a [Google Groups forum](https://groups.google.com/forum/#!forum/verifast) on VeriFast
- Kiwamu Okabe translated the VeriFast Tutorial into [Japanese](https://github.com/jverifast-ug/translate/blob/master/Manual/Tutorial/Tutorial.md). Thanks, Kiwamu!
- Joseph Benden created [Ubuntu packages](https://launchpad.net/%7Ejbenden/+archive/ubuntu/verifast)
