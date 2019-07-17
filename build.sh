#!/bin/bash

set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

if [ $(uname -s) = "Linux" ]; then

    export PATH=/tmp/vfdeps/bin:$PATH

elif [ $(uname -s) = "Darwin" ]; then

    export PKG_CONFIG_PATH=/usr/local/opt/libffi/lib/pkgconfig
    export PATH=/usr/local/vfdeps-19.07/bin:$PATH
    export DYLD_LIBRARY_PATH=/usr/local/vfdeps-19.07/lib:$DYLD_LIBRARY_PATH
  
else

    echo "Your OS is not supported by this script."
    exit 1
  
fi

cd src
make nightly VERBOSE=yes -j 2
