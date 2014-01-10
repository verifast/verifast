Building VeriFast on Linux
==========================

Contents:
0. Using the local GNUmakefile
A. Installing the build environment
B. How to build


0. Using the local GNUmakefile
===================================

Recent releases of VeriFast require OCaml >= 4.00 released in July
2012. Currently not many Linux distributions provide packages of the latest
OCaml and LABLGTK2. Thus, we provide a build script to automatically
download and compile the OCaml 4.00.1, camlidl, lablgtk and the Z3 OCaml
bindings.

You do not have to use this script, you can also install the dependencies
by hand.

The script to install the dependencies is GNUmakefile outside the src
directory. The script to build verifast itself is src/GNUmakefile.
If the script to build the dependencies does not work on your system,
you can install the dependencies by hand and just use src/GNUmakefile.

Required Packages
=================

- svn
- wget
- make
- gcc
- gtk
- standard system, X11 and GTK development files
- libgtksourceview2.0 and libgtksourceview2.0-dev

How to build
=================

- cd to the directory this README.Linux.txt is located in, we refer to this
  directory as $PWD from now on
- Run "make -f GNUmakefile" -- if you are using gnu-make, just
  "make" is sufficient
- Follow the instructions on screen, in particular with respect to
  downloading Z3
- add $PWD/z3/lib to your LD_LIBRARY_PATH environment variable:
  export LD_LIBRARY_PATH=$PWD/z3/lib:$LD_LIBRARY_PATH
- run vfide or verifast; the binaries reside in $PWD/bin

Remarks:
-----------------
- The Z3 library is a 32 bit binary. Thus, compiling and linking VeriFast
  with Z3 support requires you to have 32 bit versions of all development
  files and libraries installed
- If your Linux distribution does not provide 32 bit versions of gtk and
  libgtksourceview (e.g. the 64 bit version of Ubuntu 12.04), the build
  system will automatically skip compiling vfide, the interactive IDE of
  VeriFast. Only the command line version of the verifier will be available
  in this case.
- You may also read the GNUmakefile in advance so that you
  know what to expect
- Note that you may change download URIs and target directories in
  the preamble of GNUmakefile
- The script DOES NOT require superuser priviledges
- If a specific build step -- compiling OCaml, camlidl, lablgtk or the
  Z3 OCaml bindings -- fails, consult the README file of the particular
  package
- During compilation you will need abou 500 MBytes of free disk space on
  the volume this folder is located at



A. Installing the build environment
===================================

  +-------------------------------------------------------------------------+
  | The documentation below is outdated: The recent VeriFast depends on     |
  | OCaml >= 3.12.1, which is currently not available in a pre-packaged     |
  | form for most Linux distributions. If your distribution does not        |
  | provide packages for OCaml 3.12.1 and liblablgtksourceview2-ocaml,      |
  | follow the ABOVE instructions ("Using the local GNUmakefile").          |
  +-------------------------------------------------------------------------+

Recent releases of VeriFast require OCaml >= 3.12.0, released in May 2011.
Currently not many Linux distributions provide packages of the latest OCaml
and LABLGTK2. Thus, some massaging is required to make it work. The
instructions below will help you to install VeriFast on Debian 6.0
(squeeze) and above.

TODO: Updated instructions for Ubuntu will follow shortly. Will be similar
to Debian, though.


Required Packages
=================

svn
ocaml
ocaml-native-compilers
camlidl
libgtksourceview2.0-dev
liblablgtksourceview2-ocaml-dev (see below)


OCaml Packages
==============

Unofficial OCaml 3.12.0 packages are provided by the Debian OCamlTaskForce
(http://wiki.debian.org/Teams/OCamlTaskForce) at
http://ocaml.debian.net/debian/ocaml-3.12.0/. Although these packages are
meant to be used in Debian unstable "sid", they work fine with the current
stable and testing releases. To install OCaml, add the following two sources
to your /etc/apt/sources.list:

deb     http://ocaml.debian.net/debian/ocaml-3.12.0 sid main
deb-src http://ocaml.debian.net/debian/ocaml-3.12.0 sid main

Then do

$ apt-get update
$ apt-get install ocaml ocaml-native-compilers camlidl

If you get "unknown key" warnings, you can optionally add the key:
$ apt-key adv --keyserver keyring.debian.org --recv-keys 7853DA4D49881AD3

If you had previously installed any LABLGTK2 packages for a previous
release of OCaml, these will be removed now due to unmet dependencies:

> The following packages will be REMOVED:
>   liblablgtk2-ocaml liblablgtk2-ocaml-dev liblablgtksourceview2-ocaml
>   liblablgtksourceview2-ocaml-dev
> The following packages will be upgraded:
>   camlidl camlp4 hlins ledit liblablgtk2-ocaml-doc ocaml
>   ocaml-base ocaml-base-nox ocaml-interp ocaml-native-compilers ocaml-nox

Neither the stable Debian nor Ubuntu distributions currently provide
updated LABLGTK2 packages -- they have to be installed manually.


LABLGTK2
========

Download an unzip the sources from http://ftp.de.debian.org/:

$ wget http://ftp.de.debian.org/debian/pool/main/l/lablgtk2/lablgtk2_2.14.2+dfsg.orig.tar.gz
$ gunzip -c lablgtk2_2.14.2+dfsg.orig.tar.gz | tar -xv

Configure and compile it. To avoid interference with your package
management system, we configure LABLGTK2 to be installed in /usr/local/:

$ cd lablgtk2-2.14.2+dfsg
$ ./configure --prefix=/usr/local/ --with-libdir=/usr/local/lib/ocaml/

The output of configure will tell you the installation directories (just
remove these when you don't need LABLGTK2 any more). You will have to add
these paths to the VeriFast configuration later on:

> Install dirs are : /usr/local/lib/ocaml//lablgtk2 and
> /usr/local/lib/ocaml//stublibs
>         Compile with
>                ocamlc -I /usr/local/lib/ocaml//lablgtk2
>        and add /usr/local/lib/ocaml//stublibs either to OCAMLLIB/ld.conf
> or
>        to CAML_LD_LIBRARY_PATH

Adding a line like
    LABLGTK2 = /usr/local/lib/ocaml//lablgtk2
to GNUmakefile.settings seems to do the trick.

./configure will also tell you what features of LABLGTK2 are enabled. Make sure
that "gtksourceview 2" is set to yes and install "gtksourceview2-dev" and
dependent packages if it is not enabled:

> LablGTK configuration:
>         threads         system
>         native dynlink  yes
>         GtkGLArea       not found
>         libglade        yes
>         librsvg         not found
>         libgnomecanvas  not found
>         libgnomeui      not found
>         libpanelapplet  not found
>         gtkspell        yes
>         gtksourceview 1         not found
>         gtksourceview 2         yes        <--- important!
>         quartz          not found
> 
>         debug           no
>         C compiler      gcc

Now compile and install LABLGTK2:

$ make
$ make -C src gtkInit.cmx lablgtksourceview2.cmxa lablgtk.cmxa
$ make install
$ cp src/gtkInit.cmx src/gtkInit.o src/lablgtksourceview2.cmxa \
  src/lablgtksourceview2.a src/lablgtk.cmxa src/lablgtk.a \
  /usr/local/lib/ocaml/lablgtk2/


Z3
==

Alternative 1 (Z3 v1):
---------------
- Download Z3 v 1.3, "z3.tar.gz" from
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


Preparing the build environment
===============================

- Copy GNUmakefile.settings.exampl to GNUmakefile.settings
- Adapt it to your setup. You will usually only have to change Z3
  or Z3V2 to point to your installation of the Z3 solver.


B. How to build
===============

cd src; make clean; make

