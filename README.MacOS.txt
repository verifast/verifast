Building VeriFast on MacOS
==========================

Instructions:
- Make sure that you have Homebrew installed on your machine
- Run setup-build-with-opam.sh from the verifast folder. (This will set up the environment)
- Build and Compile VeriFast release by going to the src folder and run “make -j 8”. 


ALTERNATIVE: 
============
Note: You don’t need this if you use the above method

I successfully built VeriFast on MacOS 10.5.8.

Instructions:
- Install Xcode
- Install Ocaml
- Set up the gtk-osx build environment (with the jhbuild tool) as described at http://gtk-osx.sourceforge.net/
- Inside a jhbuild shell, build lablgtk from source
- Build VeriFast
- To isolate the Gtk files that need to be shipped with VeriFast, use the bundling tool (ige-mac-bundler) from http://gtk-osx.sourceforge.net/ to create the example gtk-demo bundle. This will generate an application at ~/Desktop/GtkDemo.app. The VeriFast release build script will get the Gtk libraries and auxiliary files from ~/Desktop/GtkDemo.app/Contents/Resources.
- Build the VeriFast release




