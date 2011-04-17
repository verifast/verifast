Building VeriFast on Linux
==========================

Contents:
A. Installing the build environment
B. How to build

A. Installing the build environment
===================================

I successfully built VeriFast on Ubuntu 9.10 (Karmic Koala, released in
October 2009) after apt-getting the packages listed in Required Packages
(using "sudo apt-get install <packagename>") and building the O'Caml
bindings for Z3 and GTK with GtkSourceView (see below). I tested the
release on Ubuntu 8.10 (Intrepid Ibex).

VeriFast also builds successfully on Ubuntu 10.10 and Debian 6.0.


Required Packages
=================

svn
ocaml
ocaml-native-compilers
camlidl
libgtksourceview2.0-dev
liblablgtksourceview2-ocaml-dev (see below)


Z3
==

Alternative 1 (Z3 v1):
---------------
- Download Z3 v 1.3, "Z3.tar.tgz" from
  https://dnetcode.cs.kuleuven.be/projects/verifast/files
- Extract it to "z3"
- run "./build-lib.sh `ocamlc -where`" in "z3/ocaml"

***does not work at the moment***
Alternative 2 (Z3 v2):
---------------
- Download Z3 v 2.XY from
  http://research.microsoft.com/projects/z3/z3-2.XY.tar.gz
- Extract it to "z3"
- run "./build-lib.sh `ocamlc -where`" in "z3/ocaml"


Lablgtk with lablgtksourceview2
===============================

Note: on Ubuntu 10.4 (Lucid Lynx) or later, and Debian 6.0 (Squeeze),
simply "sudo apt-get install liblablgtksourceview2-ocaml-dev" instead. (If
apt-get gives you Bad package errors, first install all updates recommended
by Update Manager.)

- Download lablgtk-2.14.0.tar.gz from the lablgtk website
- ./configure --with-gtksourceview2
- make world    # This will fail due to compiler errors; fix these by replacing SourceViewEnums by SourceView2Enums in the relevant source files
- sudo make install
- To run the example (optional):
  - cd examples/sourceView
  - ocamlopt.opt -o test2 -I +lablgtk2 lablgtk.cmxa gtkInit.cmx lablgtksourceview2.cmxa test2.ml
  - The above command will fail due to a bug in test2.ml. Replace lang with (Some lang) in test2.ml
  - Run the example: ./test2


Preparing the build environment
===============================

- Copy GNUmakefile.settings.exampl to GNUmakefile.settings
- Adapt it to your setup. You will usually only have to change Z3
  or Z3V2 to point to your installation of the Z3 solver.


B. How to build
===============

cd src; make

