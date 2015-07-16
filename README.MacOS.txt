Building VeriFast on MacOS
==========================

I successfully built VeriFast on MacOS 10.5.8.

Instructions:
- Install Xcode
- Install Ocaml
- Set up the gtk-osx build environment (with the jhbuild tool) as described at http://gtk-osx.sourceforge.net/
- Inside a jhbuild shell, build lablgtk from source
- Build VeriFast
- To isolate the Gtk files that need to be shipped with VeriFast, use the bundling tool (ige-mac-bundler) from http://gtk-osx.sourceforge.net/ to create the example gtk-demo bundle. This will generate an application at ~/Desktop/GtkDemo.app. The VeriFast release build script will get the Gtk libraries and auxiliary files from ~/Desktop/GtkDemo.app/Contents/Resources.
- Build the VeriFast release

