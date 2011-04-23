#!/bin/sh
MYABSDIR=$(dirname "$(readlink -f $0)")
export LD_LIBRARY_PATH="$MYABSDIR:$LD_LIBRARY_PATH"
"$MYABSDIR/verifast-core" $*
