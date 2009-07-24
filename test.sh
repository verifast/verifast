#!/bin/sh
MYRELDIR=`dirname $0`
MYABSDIR=`cd $MYRELDIR; pwd`
export PATH=$MYABSDIR/bin:$PATH
mysh < testsuite.mysh
