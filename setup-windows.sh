#!/bin/bash

# Installs OCaml and lablgtk on Windows. Called by setup-windows.bat.
#
# This script depends on (these dependencies are installed by setup-windows.bat):
#  - cygwin
#  - wget, 7z
#  - curl,make,mingw64-i686-gcc-g++,mingw64-i686-gcc-core,mingw64-i686-gcc,patch,rlwrap,libreadline6,diffutils,wget (choosen by ocaml installer)
#  - dos2unix
#  - mingw64-i686-binutils (for "ar.exe", used by vfide's makefile)

dl_and_unzip(){
  url="$1"
  filename=$(basename "$url")
  hash="$2"
  wget --progress=dot:mega -c "$url"
  echo "$hash *$filename" | sha1sum -c || exit 1
  7z -y x "$filename"
}



set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

cd /cygdrive/c

# Ocaml
# 
# The .exe OCaml installer needs GUI interaction and is thus not scriptable,
# so we extract the files and set up the config by hand.
#
# If you want to do this by hand, you can instead of executing these commands,
# just launch the .exe and keep clicking "Next".
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
echo 'export PATH="$PATH:/cygdrive/c/OCaml/bin"' >> ~/.bash_profile
      export PATH="$PATH:/cygdrive/c/OCaml/bin"
echo "export OCAMLFIND_CONF='C:\OCaml\etc\findlib.conf'" >> ~/.bash_profile
      export OCAMLFIND_CONF='C:\OCaml\etc\findlib.conf'
echo "export OCAMLLIB='C:\OCaml\lib'" >> ~/.bash_profile
      export OCAMLLIB='C:\OCaml\lib'
cd ..


# GTK
mkdir -p gtk
cd gtk
dl_and_unzip \
  ftp://ftp.gnome.org/pub/gnome/binaries/win32/gtk+/2.24/gtk+-bundle_2.24.10-20120208_win32.zip \
  895072c22f5bfd4ac9054d48d62d6c8b2a487098
cd ..

# Gtksourceview
cd gtk
dl_and_unzip \
  ftp://ftp.gnome.org/pub/gnome/binaries/win32/gtksourceview/2.10/gtksourceview-2.10.0.zip \
  9d04bdeb86ed8358e250394a35e389680b5c8bf5
dl_and_unzip \
  ftp://ftp.gnome.org/pub/gnome/binaries/win32/gtksourceview/2.10/gtksourceview-dev-2.10.0.zip \
  2accab71c2c4b6bae91453e5428a7ef37a45fbe3
dl_and_unzip \
  ftp://ftp.gnome.org/pub/gnome/binaries/win32/dependencies/libxml2_2.9.0-1_win32.zip \
  a7961070b8a954c36041b7cc1948213a5195f043
dl_and_unzip \
  ftp://ftp.gnome.org/pub/gnome/binaries/win32/dependencies/libxml2-dev_2.9.0-1_win32.zip \
  6bedf32091e78764c2121db63b6927967c9e4844
cd ..

# LablGTK
wget -c http://forge.ocamlcore.org/frs/download.php/1261/lablgtk-2.18.3.tar.gz
echo "c76a7ae9454e89365666cf19728dbb51edb6810e2e57032b3bebd53ccec5946e *lablgtk-2.18.3.tar.gz" | sha256sum -c || exit 1
tar -xzf lablgtk-2.18.3.tar.gz
mv lablgtk-2.18.0 lablgtk-2.18.3 # Bug in lablgtk-2.18.3.tar.gz: the directory is still called lablgtk-2.18.0
cd lablgtk-2.18.3
# Problem: the pkg-config program that ships with Gtk produces CRLF-terminated
#          lines. The Cygwin tools choke on this.
# Solution: create a wrapper that transforms the DOS lines to Unix lines using
#           Cygwin's "conv --dos2unix" or dos2unix program:
cat << EOF > pkg-config
#!/bin/bash
set -o pipefail # A pipe fails if any component fails
/cygdrive/c/gtk/bin/pkg-config \$* | dos2unix
EOF
chmod +x pkg-config
echo 'export CAMLP4LIB=C:/OCaml/lib/camlp4' >> ~/.bash_profile
      export CAMLP4LIB=C:/OCaml/lib/camlp4
echo 'export PATH="/cygdrive/c/lablgtk-2.18.3:/cygdrive/c/gtk/bin:$PATH"' >> ~/.bash_profile
      export PATH="/cygdrive/c/lablgtk-2.18.3:/cygdrive/c/gtk/bin:$PATH"
./configure
make
make opt
#In src/Makefile, after the line
#  include $(CONFIG)
#insert the line
#  FLINSTALLDIR := $(subst \,/,$(FLINSTALLDIR))
sed -i 's/include \$(CONFIG)/include \$(CONFIG)\nFLINSTALLDIR := \$(subst \\,\/,\$(FLINSTALLDIR)\)\n/' src/Makefile
make install
cd ..

# Hack to make "ar" work in makefiles
which ar 2>/dev/null || ln -s $(which i686-w64-mingw32-ar.exe) /usr/bin/ar
