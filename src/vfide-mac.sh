#!/bin/sh
MYRELDIR=`dirname $0`
MYABSDIR=`cd $MYRELDIR; pwd`
export DYLD_LIBRARY_PATH=$MYABSDIR/../lib:$DYLD_LIBRARY_PATH
export GDK_PIXBUF_MODULE_FILE=$MYABSDIR/../etc/gtk-2.0/gdk-pixbuf.loaders
"$MYABSDIR/vfide-core" "$@"
