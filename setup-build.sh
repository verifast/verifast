#!/bin/bash

#
# Installs dependencies, builds VeriFast, and runs tests.
# Suitable for home use and for continuous integration.
#
# Supported: vfide
# Not supported: z3
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
  brewinstall ocaml
  brewinstall ocaml-num
  brewinstall lablgtk
  brewinstall camlp4
  export PKG_CONFIG_PATH=/opt/X11/lib/pkgconfig
  
else
  echo "Your OS is not supported by this script."
  exit 1
  
fi
