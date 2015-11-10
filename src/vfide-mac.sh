#!/bin/sh
MYRELDIR=`dirname "$0"`
MYABSDIR=`cd "$MYRELDIR"; pwd`
export DYLD_LIBRARY_PATH="$MYABSDIR/../lib:$DYLD_LIBRARY_PATH"
export GDK_PIXBUF_MODULE_FILE="$MYABSDIR/../lib/gdk-pixbuf-2.0/2.10.0/loaders.cache"
export PANGO_LIBDIR="$MYABSDIR/../lib"
export PANGO_SYSCONFDIR="$MYABSDIR/../etc"
"$MYABSDIR/vfide-core" "$@"
