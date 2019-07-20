#!/bin/bash

#
# Installs dependencies, builds VeriFast, and runs tests.
# Suitable for home use and for continuous integration.
#

set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

. ./config.sh

if [ $(uname -s) = "Linux" ]; then
  sudo apt-get update
  sudo apt-get install -y --no-install-recommends \
       git wget ca-certificates make m4 \
       gcc patch unzip libgtk2.0-dev \
       valac libgtksourceview2.0-dev
  cd /tmp && curl -Lf https://dl.bintray.com/verifast/verifast/$VFDEPS_NAME-linux.txz | tar xj

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
  sudo mkdir /usr/local/$VFDEPS_NAME
  sudo chown -R $(whoami):admin /usr/local/*
  cd /usr/local && curl -Lf https://dl.bintray.com/verifast/verifast/$VFDEPS_NAME-macos.txz | tar xj
  
else
  echo "Your OS is not supported by this script."
  exit 1
  
fi
