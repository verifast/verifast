How to build VeriFast
=====================

Outputs
-------

You can build multiple outputs, depending on the following:
- Do you want the command-line tool (verifast) or the IDE (vfide, depends on the GTK DLLs)?
- Do you want the machine code version (.opt, does not print exception stack traces) (runs faster) or the bytecode version (compiles faster, prints exception stack traces)?
- Do you want to include Redux (not as good as Z3 (yet ;-) )?
- Do you want to include Z3 (depends on Z3.dll)?

So that's 12 possible outputs. The Makefile does not support all of them yet, though. Some supported ones:

nmake verifastz3.opt.exe
nmake vfidez3.opt.exe

In order to build and run VeriFast, a number of environment variables need to be set. You can do this conveniently by creating a settings.bat file. Do

copy settings.bat.example settings.bat

and edit settings.bat to update the paths as appropriate for your setup.

Z3
--

VeriFast uses the Z3 Ocaml API.

1) Download and run the Z3 .msi file from http://research.microsoft.com/projects/z3/

2) Download and unzip the CamlIDL sources .zip file from http://caml.inria.fr/pub/old_caml_site/camlidl/

3) Install CamlIDL as per the README file. Specifically, in a Cygwin shell started from a Visual Studio command prompt (so that the Visual C++ compiler (cl.exe) is in the PATH):
  3.1) Copy config/Makefile.win32 to config/Makefile
  3.2) If your Ocaml is not in C:\Ocaml, edit OCAMLLIB and BINDIR in config/Makefile
  3.3) Do

           where link

       to check that Visual C++'s LINK.EXE is not hidden by GCC 'link'. If it is, do

           export PATH=/cygdrive/c/Program\ Files/Visual\ Studio\ 8/VC/bin:$PATH

  3.4) Do 'make all'
  3.5) Assuming you have write access to your Ocaml installation, do 'make install'

4) Build the Z3 Ocaml API
  4.1) In Z3's ocaml directory, do 'build.cmd'
  4.2) Optionally, test it by going to Z3's examples\ocaml directory and doing 'build' and then 'exec'

LablGTK
-------

VeriFast uses LablGTK, an OCaml language binding for the GTK GUI toolkit.
To build and run VeriFast, you must first download and install GTK and
LablGTK, as follows:

1) Download and unzip the GTK bundle:

http://ftp.gnome.org/pub/gnome/binaries/win32/gtk+/2.12/gtk+-bundle-2.12.11.zip

2) Download and unzip the LablGTK bundle:

http://wwwfun.kurims.kyoto-u.ac.jp/soft/lsl/dist/lablgtk-2.10.1-win32.zip

3) Build LablGTK:

cd <lablgtkdir>\lib\lablgtk2
ocaml build.ml

4) Install LablGTK:

xcopy /E <lablgtkdir>\lib\lablgtk2 <ocamldir>\lib
xcopy <lablgtkdir>\lib\stublibs\dlllablgtk2.dll <ocamldir>\lib\stublibs
xcopy <lablgtkdir>\bin\labkgtk2.bat <ocamldir>\bin

Before running a program that uses GTK, put the GTK DLLs in your PATH:

set PATH=<gtkdir>\bin;%PATH%
