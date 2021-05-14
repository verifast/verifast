#!/bin/bash

#
# Installs dependencies, builds VeriFast, and runs tests.
# Suitable for home use and for continuous integration.
#

dl_and_unzip() {
  url="$1"
  filename=$(basename "$url")
  hash="$2"
  curl -Lf -o "/tmp/$filename" "$url"
  echo "$hash  /tmp/$filename" | shasum -a 224 -c || exit 1
  tar xjf "/tmp/$filename"
}

set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

. ./config.sh

if [ $(uname -s) = "Linux" ]; then
  sudo apt-get update
  sudo apt-get install -y --no-install-recommends \
       git wget ca-certificates make m4 \
       gcc patch unzip libgtk2.0-dev \
       valac libgtksourceview2.0-dev
  cd /tmp
  dl_and_unzip https://people.cs.kuleuven.be/~bart.jacobs/verifast/$VFDEPS_NAME-linux.txz 9f502036a859e163d4ad06b4b01ac21ac91564fda913b0dc88819eb3

elif [ $(uname -s) = "Darwin" ]; then

  if [ -z "$GITHUB_ACTIONS" ]; then
      # No need to update when running in GitHub Actions; their brew is updated weekly.
      brew update
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
  cd /usr/local
  dl_and_unzip https://people.cs.kuleuven.be/~bart.jacobs/verifast/$VFDEPS_NAME-macos.txz ba2f1567e7ed74d1cec47b0fed60522df6a8f4f0155f4347fda78f2d
  
else
  echo "Your OS is not supported by this script."
  exit 1
  
fi
