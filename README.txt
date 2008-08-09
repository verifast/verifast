How to build VeriFast
=====================

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
