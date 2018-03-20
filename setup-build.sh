#!/bin/bash

#
# Installs dependencies, builds VeriFast, and runs tests.
# Suitable for home use and for continuous integration.
#

set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

if [ $(uname -s) = "Linux" ]; then
  sudo apt-get install -y --no-install-recommends \
       git wget ca-certificates make m4 \
       gcc patch unzip libgtk2.0-dev \
       valac gtksourceview2.0-dev
  cd /tmp && curl -Lf http://people.cs.kuleuven.be/~bart.jacobs/verifast/vfdeps-ocaml-4.06.0-trusty.tar.xz | tar xj

elif [ $(uname -s) = "Darwin" ]; then
  brew update

  if [ $TRAVIS = "true" ]; then
      brew unlink python # See https://github.com/verifast/verifast/issues/127
  fi

  function brewinstall {
      if brew list $1 1>/dev/null 2>/dev/null; then
	  true;
      else
	  brew install $1;
      fi
  }  
  brewinstall wget
  brewinstall gtk+
  brewinstall gtksourceview
  brewinstall vala
  export PKG_CONFIG_PATH=/opt/X11/lib/pkgconfig
  sudo chown -R $(whoami):admin /usr/local
  cd /usr/local && curl -Lf http://people.cs.kuleuven.be/~bart.jacobs/verifast/vfdeps-17.12-el-capitan.txz | tar xj
  export PATH=/usr/local/vfdeps-17.12/bin:$PATH
  export DYLD_LIBRARY_PATH=/usr/local/vfdeps-17.12/lib:$DYLD_LIBRARY_PATH
  
else
  echo "Your OS is not supported by this script."
  exit 1
  
fi
