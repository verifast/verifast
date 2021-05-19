#!/bin/bash

#
# Installs dependencies, builds VeriFast, and runs tests.
# Suitable for home use and for continuous integration.
#

llvm_version=13

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

script_dir=$(pwd)

if [ $(uname -s) = "Linux" ]; then
  wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key|sudo apt-key add -
  sudo apt-add-repository "deb http://apt.llvm.org/bionic/ llvm-toolchain-bionic-$llvm_version main"
  sudo apt-get update
  sudo apt-get install -y --no-install-recommends \
       git wget ca-certificates make m4 \
       gcc patch unzip libgtk2.0-dev \
       valac libgtksourceview2.0-dev \
       make cmake llvm-$llvm_version-dev clang-$llvm_version libclang-$llvm_version-dev
  cd /tmp
  dl_and_unzip https://vfdeps-cxx-linux.herokuapp.com/$VFDEPS_NAME-linux.txz c69e9bb1f058d827727d28922f3ebb6353f2fcbc8bd7dfe3ece54f94
  cd ..
  cd $script_dir/src/cxx_frontend/ast_exporter/build
  CC=/usr/bin/clang-$llvm_version CXX=/usr/bin/clang++-$llvm_version cmake -DLLVM_INSTALL_DIR=/usr/lib/llvm-$llvm_version -DVFDEPS=/tmp/$VFDEPS_NAME -DCMAKE_BUILD_TYPE=Debug ..


elif [ $(uname -s) = "Darwin" ]; then

  # if [ -z "$GITHUB_ACTIONS" ]; then
      # No need to update when running in GitHub Actions; their brew is updated weekly.
      brew update
  # fi

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
  brewinstall cmake
  brewinstall llvm@$llvm_version
  export PKG_CONFIG_PATH=/opt/X11/lib/pkgconfig
  sudo mkdir /usr/local/$VFDEPS_NAME
  sudo chown -R $(whoami):admin /usr/local/*
  cd /usr/local
  dl_and_unzip https://vfdeps-cxx-macos.herokuapp.com/$VFDEPS_NAME-macos.txz 301bf548e6bdbaac79ef49f3c2eb787a37b8487c4c25de1aec92b6c5
  cd $script_dir/src/cxx_frontend/ast_exporter/build
  cmake -DLLVM_INSTALL_DIR=$(brew --prefix llvm@$llvm_version) -DVFDEPS=/usr/local/$VFDEPS_NAME -DCMAKE_BUILD_TYPE=Debug ..
  
else
  echo "Your OS is not supported by this script."
  exit 1
  
fi
