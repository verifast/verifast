#!/bin/bash

set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

. ./config.sh

if [ $(uname -s) = "Linux" ]; then

    export PATH=/tmp/$VFDEPS_NAME/bin:$PATH

elif [ $(uname -s) = "Darwin" ]; then

    export PKG_CONFIG_PATH=/usr/local/opt/libffi/lib/pkgconfig
    export PATH=/usr/local/$VFDEPS_NAME/bin:$PATH
    export DYLD_LIBRARY_PATH=/usr/local/$VFDEPS_NAME/lib:$DYLD_LIBRARY_PATH
  
else

    echo "Your OS is not supported by this script."
    exit 1
  
fi

cd src
make nightly VERBOSE=yes -j 2
