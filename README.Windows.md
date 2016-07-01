Building VeriFast for Windows
=============================


Note: this creates extra directories in C:\

1. Place VeriFast's files in `c:\projects\verifast`
   (the scripts expect it to be there)
2. Launch `c:\projects\verifast\setup-windows.bat`
3. Open Windows' commandline and execute
     `c:\cygwin\bin\bash -lc "cd /cygdrive/c/projects/verifast/src && make VERBOSE=yes"`
4. vfide can now be launched from `c:\projects\verifast\bin\vfide.exe`

Te recompile, you only need to re-execute step 3.


ALTERNATIVE: Building by hand
-----------------------------

```
This builds native Win32 VeriFast executables that do not depend on Cygwin, but the build
process requires Cygwin.

- Install the "Cygwin-based native Win32 port" of OCaml by running the installer linked from the OCaml "Latest release" web page at http://caml.inria.fr/.
  URL: http://gallium.inria.fr/~protzenk/caml-installer/ocaml-4.02.3-i686-mingw64-installer4.exe
  Install all optional components, including Cygwin itself. (If Cygwin is already installed, this will just install any missing Cygwin packages, including
  the gcc-mingw Cygwin-to-MinGW cross-compiler.
  To keep Cygwin from messing with Windows file permissions, edit /etc/fstab and add ",noacl" to the mount options of each NTFS mount (including in particular the /cygdrive mount).
  At this point, you should be able to successfully build VeriFast in its default configuration (no Z3, no IDE)
  and successfully run the test suite. (Test cases that require Z3 will be skipped).
  To do so, run

    cd src; make WITHOUT_LABLGTK=yes

To enable Z3 support:
- Build and install camlidl.

wget http://caml.inria.fr/pub/old_caml_site/distrib/bazar-ocaml/camlidl-1.05.tar.gz
tar xzf camlidl-1.05.tar.gz
cd camlidl-1.05
cp config/Makefile.unix config/Makefile

Now, edit config/Makefile and update the lines that set OCAMLLIB and BINDIR as follows (assuming C:\OCaml4010 is the location of your OCaml installation):
OCAMLLIB=C:/OCaml4010/lib
BINDIR=/cygdrive/c/OCaml4010/bin

make all
make install

- Build the Z3 OCaml bindings.
Download https://dnetcode.cs.kuleuven.be/attachments/download/1030/Z3-1.3.6-win.tgz (you'll have to log in)
tar xzf Z3-1.3.6-win.tgz
cd Z3-1.3.6
cp -R ocaml ocaml-clean
cd ocaml
ocamlopt.opt -ccopt "-I ../include" -c z3_stubs.c
ocamlopt.opt -a -o z3.cmxa -ccopt `cygpath -m "$PWD/../bin/z3.lib"` z3_stubs.o z3.mli z3.ml -cclib -lole32 -cclib -lcamlidl

To test:
cd ../examples/ocaml
ocamlopt.opt -o test_mlapi.exe -I ../../ocaml z3.cmxa test_mlapi.ml
PATH=../../bin:$PATH ./test_mlapi

To enable in the VeriFast build process: in <VeriFast checkout>/GNUmakefile.settings:
- replace the line
    NOZ3=...
  by
    #NOZ3=...
- replace the line
    #Z3=...
  by something like
    Z3=/cygdrive/c/Z3-1.3.6

To build the IDE:

Inside Cygwin:

wget ftp://ftp.gnome.org/pub/gnome/binaries/win32/gtk+/2.24/gtk+-bundle_2.24.10-20120208_win32.zip
mkdir gtk
cd gtk
unzip ../gtk+-bundle_2.24.10-20120208_win32.zip
cd ..
wget https://forge.ocamlcore.org/frs/download.php/1261/lablgtk-2.18.3.tar.gz
tar xzf lablgtk-2.18.3.tar.gz
mv lablgtk-2.18.0 lablgtk-2.18.3 # Bug in lablgtk-2.18.3.tar.gz: the directory is still called lablgtk-2.18.0
cd lablgtk-2.18.3

Problem: the pkg-config program that ships with Gtk produces CRLF-terminated lines. The Cygwin tools choke on this.
Solution: create a wrapper that transforms the DOS lines to Unix lines using the Cygwin conv program:

Create file pkg-config with the following contents:
#!/bin/bash
set -o pipefail # A pipe fails if any component fails
/cygdrive/c/gtk/bin/pkg-config $* | conv --dos2unix

export PATH=$PWD:/usr/bin:/cygdrive/c/OCaml4010/bin:/cygdrive/c/gtk/bin
./configure
export CAMLP4LIB=C:/OCaml4023/lib/camlp4
make
make opt
In src/Makefile, after the line
  include $(CONFIG)
insert the line
  FLINSTALLDIR := $(subst \,/,$(FLINSTALLDIR))
make install

Note: the lablgtk2 wrapper for the ocaml toplevel is installed into /usr/local/bin, but is broken (because the backslashes in the OCaml directory name are expanded away).

To test:
cd examples
ocaml -I +site-lib/lablgtk2 lablgtk.cma gtkInit.cmo hello.ml
ocaml -I +site-lib/lablgtk2 lablgtk.cma gtkInit.cmo testgtk.ml

Note: to run vfide, you first need to add the GTK bin directory to your PATH. If you try to run vfide from the Cygwin terminal without having GTK in your PATH, it will give you the error message

    C:/VeriFast/workdir/bin/vfide.exe: error while loading shared libraries: Z3.dll: cannot open shared object file: No such file or directory

even if Z3.dll is in your PATH and the problem is really that the GTK DLLs are not in your PATH!

Getting gtksourceview2 support:
wget ftp://ftp.gnome.org/pub/gnome/binaries/win32/gtksourceview/2.10/gtksourceview-2.10.0.zip
wget ftp://ftp.gnome.org/pub/gnome/binaries/win32/gtksourceview/2.10/gtksourceview-dev-2.10.0.zip
wget ftp://ftp.gnome.org/pub/gnome/binaries/win32/dependencies/libxml2_2.9.0-1_win32.zip
wget ftp://ftp.gnome.org/pub/gnome/binaries/win32/dependencies/libxml2-dev_2.9.0-1_win32.zip
Extract into C:\gtk
(To check that you have all dependencies, run pkg-config --cflags gtksourceview-2.0. This will tell you which packages are unresolved, if any.)
./configure
make
make opt
make install # (if this fails, do make uninstall first)

To test:
cd examples/sourceview
ocaml -I +site-lib/lablgtk2 lablgtk.cma gtkInit.cmo lablgtksourceview2.cma test2.ml

```
