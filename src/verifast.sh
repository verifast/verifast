#/bin/bash
MYRELDIR=`dirname $0`
MYABSDIR=`cd $MYRELDIR; pwd`
export LD_LIBRARY_PATH=$MYABSDIR:$LD_LIBRARY_PATH
$MYABSDIR/verifast-core $*
