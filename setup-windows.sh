#!/bin/bash

# Installs OCaml on Windows. Called by setup-windows.bat.
#
# The .exe OCaml installer needs GUI interaction and is thus not scriptable,
# so we extract the files by hand.
#
# This script depends on (these dependencies are installed by setup-windows.bat):
#  - cygwin
#  - wget, 7z
#  - curl,make,mingw64-i686-gcc-g++,mingw64-i686-gcc-core,mingw64-i686-gcc,patch,rlwrap,libreadline6,diffutils,wget (choosen by ocaml installer)

set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

cd /cygdrive/c
mkdir -p OCaml
cd OCaml
wget --progress=dot:mega -c http://gallium.inria.fr/~protzenk/caml-installer/ocaml-4.02.3-i686-mingw64-installer4.exe
echo "64cfe42bd15d059cb3ad2916bfa234b555f1d355 *ocaml-4.02.3-i686-mingw64-installer4.exe" | sha1sum -c || exit 1
7z -y x ocaml-4.02.3-i686-mingw64-installer4.exe bin/ lib/
chmod +x bin/*
chmod a+rx lib lib/ lib/stublibs lib/stublibs/*
mkdir -p etc
cat << EOF > etc/findlib.conf
destdir="C:\\\\OCaml\\\\lib\\\\site-lib"
path="C:\\\\OCaml\\\\lib\\\\site-lib"
stdlib="C:\\\\OCaml\\\\lib"
ldconf="C:\\\\OCaml\\\\lib\\\\ld.conf"
ocamlc="ocamlc.opt"
ocamlopt="ocamlopt.opt"
ocamldep="ocamldep.opt"
ocamldoc="ocamldoc.opt"
EOF
echo 'C:\OCaml\lib' > lib/ld.conf
echo 'C:\OCaml\lib\stublibs' >> lib/ld.conf

echo 'export PATH=/cygdrive/c/OCaml/bin:$PATH' >> ~/.bash_profile
echo "export OCAMLFIND_CONF='C:\OCaml\etc\findlib.conf'" >> ~/.bash_profile
echo "export OCAMLLIB='C:\OCaml\lib'" >> ~/.bash_profile
