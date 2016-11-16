Compiling VeriFast on Linux
===========================

Debian-based (Ubuntu, Mint, ...) (32bit + 64bit)
----------------------------------------
    
    
1.  Run this
    
  ```sh    
  $ sudo apt-get install --no-install-recommends \
      git wget ca-certificates make m4 \
      ocaml-native-compilers gcc camlp4 patch unzip libgtk2.0-dev \
      valac gtksourceview2.0-dev \
      liblablgtk2-ocaml-dev liblablgtksourceview2-ocaml-dev
  $ git clone https://github.com/verifast/verifast.git
  $ make -j 8 -C verifast/src/
  $ verifast/bin/vfide
  ```

2.  Enjoy!



 
--- TEXT BELOW IS OUTDATED ---
ALTERNATIVE: using Opam
-----------------------

Note: you do not need this if you use the above method.

1. Note: without `gtksourceview2.0-dev`, `opam` builds `lablgtk` with `sourceview` bindings missing
   ```sh
   sudo apt-get install --no-install-recommends wget ca-certificates make m4 gcc patch unzip libgtk2.0-dev subversion valac gtksourceview2.0-dev
   mkdir -p ~/.local/bin
   wget https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh -O - | sh -s ~/.local/bin
   export PATH=$PATH:~/.local/bin
   echo 'export PATH=$PATH:~/.local/bin' >> ~/.bashrc
   eval `opam config env`
   echo "eval `opam config env`" >> ~/.bashrc
   opam init --comp=4.02.1
   opam install core lablgtk camlidl
   VERIFASTDIR=$PWD
   svn co --username USERNAME https://dnetcode.cs.kuleuven.be/svn/verifast/verifast/trunk verifast
   cd verifast/src/
   make -j 8
   ../bin/vfide
   ```
   
2. Enjoy!
     
    
    
Z3 on 32bit (OPTIONAL)
----------------------

Note: only tested with apt-get approach above, not with the Opam approach.

3.  `sudo apt-get install camlidl`

4.  Download (requires login)
    https://dnetcode.cs.kuleuven.be/attachments/download/736/z3.tar.gz

5.  Run this (replace DOWNLOADPATH with the directory you put z3.tar.gz in (in step 4))
    ```sh
    $ cd
    $ Z3DIR=$PWD
    $ tar -xzf DOWNLOADPATH/z3.tar.gz
    $ cd z3/ocaml
    ```
    
6.  Ignore the warnings on this one:
    ```sh
    $ ./build-lib.sh $(ocamlc -where)
    $ echo "Z3=$PWD/../" >> $VERIFASTDIR/verifast/src/../GNUmakefile.settings
    ```
    
7.  Recompile VeriFast:
    ```sh
    $ cd $VERIFASTDIR/verifast/src/
    $ make -j 8
    ```

8.  Run
    ```sh
    $ export LD_LIBRARY_PATH="$Z3DIR/z3/lib:$LD_LIBRARY_PATH"
    $ $VERIFASTDIR/verifast/bin/vfide
    ```


What about Z3 on 64bit? (OPTIONAL)
-----------------------

libz3.so is a 32bit library, so you cannot simply link it from a 64 bit
executable.
However, you can compile verifast as 32bit application (including Z3) and run
that 32bit application in a 64bit Linux installation.
Instructions how to run 32bit VeriFast on a 64bit Ubuntu can be found in
Z3-on-Ubuntu64.txt



