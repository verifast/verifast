Compiling VeriFast on Debian and Ubuntu (also works on 64bit)
=======================================
    
    
1.  Run this (replace USERNAME with your departemental username)
    
    $ sudo apt-get install --no-install-recommends \
       subversion make ocaml-native-compilers gcc camlp4 \
       liblablgtk2-ocaml-dev liblablgtksourceview2-ocaml-dev valac
    $ VERIFASTDIR=$PWD
    $ svn co --username USERNAME https://dnetcode.cs.kuleuven.be/svn/verifast/verifast/trunk verifast
    $ cd verifast/src/
    $ make -j 8
    $ ../bin/vfide

2.  Enjoy!
    
    

Multiple Ocaml versions (optional)
=======================
If using Opam and if Opam works, you can test on multiple ocaml versions:
    $ opam switch 4.02.0
    $ opam install core lablgtk camlidl
     
    
    
Getting Z3 working on 32bit (optional)
===========================

3.  Download (requires login)
    https://dnetcode.cs.kuleuven.be/attachments/download/736/z3.tar.gz

4.  Run this (replace DOWNLOADPATH with the directory you put z3.tar.gz in (in step 3))
    $ cd
    $ Z3DIR=$PWD
    $ tar -xzf DOWNLOADPATH/z3.tar.gz
    $ cd z3/ocaml

5.  Ignore the warnings on this one:
    $ ./build-lib.sh $(ocamlc -where)
    $ echo "Z3=$PWD/../" >> $VERIFASTDIR/verifast/src/../GNUmakefile.settings
    
5.  Recompile VeriFast:
    $ cd $VERIFASTDIR/verifast/src/
    $ make -j 8

6.  Run
    $ export LD_LIBRARY_PATH="$Z3DIR/z3/lib:$LD_LIBRARY_PATH"
    $ $VERIFASTDIR/verifast/bin/vfide





What about Z3 on 64bit?
=======================

libz3.so is a 32bit library, so you cannot simply link it from a 64 bit
executable.
However, you can compile verifast as 32bit application (including Z3) and run
that 32bit application in a 64bit Linux installation.
Instructions how to run 32bit VeriFast on a 64bit Ubuntu can be found in
Z3-on-Ubuntu64.txt



