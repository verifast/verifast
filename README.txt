How to build VeriFast on Win32
==============================

In order to build VeriFast on an x86 Windows machine, you need to
1) Install the required software packages
2) Set environment variables
3) Run nmake in the src directory

1) Install Required Software Packages
=====================================

You can either use tools.zip, which contains all required tools (except Visual Studio),
or you can do a manual install.

i) Use tools.zip
----------------

Simply download tools.zip from https://aramis.cs.kuleuven.be/verifast/chrome/site/tools.zip and unzip it to C:\.

Note: unfortunately, the tools are not relocatable. I installed them to C:\, so you
MUST unzip them to C:\ as well.

ii) Manual install
------------------

You also need Microsoft Visual C++ 8.0 (Visual Studio 2005) or newer.

A. OCaml 3.11 or newer
B. Flexdll 0.14 or newer
C. Cygwin; GNU make (to build Camlidl)
D. Camlidl 1.05 or newer
E. Z3 1.3.6 or newer
F. LablGTK 2.12.0 or newer

A. OCaml
--------

VeriFast is written in O'Caml.

1) Download the OCaml 3.11 Windows binaries (for the Microsoft Visual C++ toolchain) and install it.
2) Add the bin directory to your PATH
3) set OCAMLLIB=C:\Ocaml311\lib

B. Flexdll
----------

Flexdll is a flexible, Unix-like linker used by O'Caml.

1) Download it and unzip it
2) Put it in your PATH

C. Cygwin
---------

Cygwin is needed to build Camlidl, which is needed for the Z3 O'Caml binding. VeriFast uses the Z3 SMT solver.

1) Install Cygwin
2) Install the GNU make package

D. Camlidl
----------

Camlidl is needed for the Z3 O'Caml binding. VeriFast uses the Z3 SMT solver.

1) Download and unzip the CamlIDL sources .zip file from http://caml.inria.fr/pub/old_caml_site/camlidl/

2) Install CamlIDL as per the README file. Or see here.
  Unfortunately, this requires Cygwin. Important: before starting Cygwin, set the CYGWIN=nontsec environment variable.
  In a Cygwin shell started from a Visual Studio command prompt (so that the Visual C++ compiler (cl.exe) is in the PATH):
  3.1) Copy config/Makefile.win32 to config/Makefile
  3.2) If your Ocaml is not in C:\Ocaml, edit OCAMLLIB and BINDIR in config/Makefile
  3.3) Do

           where link

       to check that Visual C++'s LINK.EXE is not hidden by GCC 'link'. If it is, do

           export PATH=/cygdrive/c/Program\ Files/Microsoft\ Visual\ Studio\ 9.0/VC/bin:$PATH

  3.4) Do 'make all'
  3.5) Assuming you have write access to your Ocaml installation, do 'make install'

E. Z3
-----

VeriFast uses the Z3 SMT solver.

1) Download and run the Z3 .msi file from http://research.microsoft.com/projects/z3/

2) Build the Z3 Ocaml API
  4.1) In Z3's ocaml directory, issue the following commands (do not use build.cmd):

           ocamlopt -ccopt "/DWIN32 /I ..\include" -c z3_stubs.c z3.mli z3.ml
           ocamlopt -a -o z3.cmxa ..\bin\z3.lib z3_stubs.obj z3.cmx ole32.lib libcamlidl.lib

  4.2) Optionally, test it
    a) Go to Z3's examples\ocaml directory
    b) Issue the following command:

           ocamlopt -o test_mlapi.exe -I ..\..\ocaml z3.cmxa test_mlapi.ml

    c) Run exec.cmd

F. LablGTK
----------

VeriFast uses LablGTK, an OCaml language binding for the GTK GUI toolkit.
To build and run VeriFast, you must first download and install GTK and
LablGTK, as follows:

1) Download and unzip the GTK bundle:

http://ftp.gnome.org/pub/gnome/binaries/win32/gtk+/2.12/gtk+-bundle-2.12.11.zip

2) Download and unzip the LablGTK bundle:

http://wwwfun.kurims.kyoto-u.ac.jp/soft/olabl/dist/lablgtk-2.12.0-win32.zip

3) Build LablGTK:

cd <lablgtkdir>\lib\lablgtk2
ocaml build.ml

4) Install LablGTK:

xcopy /E C:\lablgtk\lib\lablgtk2 C:\ocaml\lib
xcopy C:\lablgtk\lib\stublibs\dlllablgtk2.dll C:\ocaml\lib\stublibs
xcopy C:\lablgtk\bin\lablgtk2.bat C:\ocaml\bin

Before running a program that uses GTK, put the GTK DLLs in your PATH:

set PATH=<gtkdir>\bin;%PATH%

2) Set Environment Variables
============================

In order to build and run VeriFast, a number of environment variables need to be set. You can do this conveniently by creating a settings.bat file. Do

copy settings.bat.example settings.bat

and edit settings.bat to update the paths as appropriate for your setup.
(If you unzipped tools.zip, most paths are already correct.)

It is convenient to create a "VeriFast Command Prompt" by copying the "Command Prompt" shortcut and modifying the command line to read as follows:

C:\WINDOWS\system32\cmd.exe /k C:\verifast\settings.bat

3) Run Nmake
============

Go to the src directory, and run nmake. You will get verify.exe and vfide.exe in the src directory.
The makefile will also run the test suite.
You might want to put the src directory in your PATH.
