Building VeriFast on Linux
==========================

I successfully built VeriFast on Ubuntu 9.10 (Karmic Koala, released in October 2009) after apt-getting the packages listed in Required Packages (using "sudo apt-get install <packagename>") and building the O'Caml bindings for Z3 and GTK with GtkSourceView (see below). I tested the release on Ubuntu 8.10 (Intrepid Ibex).

Required Packages
=================

svn
ocaml
ocaml-native-compilers
camlidl
libgtksourceview2.0-dev

Z3
==

- Download Z3.tar.tgz from https://aramis.cs.kuleuven.be/verifast
- Extract it
- run ./build-lib.sh `ocamlc -where`

Lablgtk with lablgtksourceview2
===============================

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

- Copy settings.sh.example to settings.sh
- Adapt it to your setup
- Source it: . settings.sh

To build
========

cd src; make
