Building VeriFast on Linux
==========================

I successfully built VeriFast on Ubuntu 8.10 (Intrepid Ibex, released in October 2008) after apt-getting the following packages and their dependencies:

subversion
ocaml-nox
ocaml-native-compilers
liblablgtk2-ocaml-dev
camlidl


1) Download Z3.tar.tgz from https://aramis.cs.kuleuven.be/verifast; extract it; run ./build-lib.sh `ocamlc -where`
2) Copy settings.sh.example to settings.sh; adapt it to your setup; source it.
3) cd src; make
