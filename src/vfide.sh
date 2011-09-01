#!/bin/sh
MYABSPATH=$(readlink -f "$0")
MYABSDIR=$(dirname "$MYABSPATH")
export LD_LIBRARY_PATH="$MYABSDIR:$LD_LIBRARY_PATH"
"$MYABSDIR/vfide-core" "$@"
