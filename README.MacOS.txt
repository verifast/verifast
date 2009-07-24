Building VeriFast on MacOS
==========================

I successfully built VeriFast on MacOS 10.5.7.

Instructions:
- Install Xcode
- Install Ocaml
- Install pkg-config
- Install GTK
- Configure pkg-config for GTK:

export PKG_CONFIG_PATH=\
/Library/Frameworks/GLib.framework/Resources/dev/lib/pkgconfig:\
/Library/Frameworks/Cairo.framework/Resources/dev/lib/pkgconfig:\
/Library/Frameworks/Gtk.framework/Resources/dev/lib/pkgconfig

- Install lablgtk
- Add the src directory to your PATH:

export PATH=~/verifast/src:$PATH

- Make verifast with MAC=yes:

make MAC=yes
