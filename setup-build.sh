#!/bin/bash

#
# Installs dependencies, builds VeriFast, and runs tests.
# Suitable for home use and for continuous integration.
#

set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

. ./config.sh

dl_and_unzip() {
  url="$1"
  filename=$(basename "$url")
  hash="$2"
  sha="$3"
  filter="$4"
  curl -Lf -o "/tmp/$filename" "$url"
  echo "$hash  /tmp/$filename" | shasum -a "$sha" -c || exit 1
  tar "x"$filter"f" "/tmp/$filename"
}

dl_and_unzip_vfdeps() {
  url="$1"
  hash="$2"
  dl_and_unzip $url $hash 224 j
}

dl_and_unzip_llvm-clang() {
  platform="$1"
  hash="$2"
  dl_and_unzip "https://github.com/NielsMommen/vf-llvm-clang-build/releases/download/v1.0.0/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION-$platform.tar.gz" $hash 256 z
}

script_dir=$(pwd)

if [ $(uname -s) = "Linux" ]; then
  sudo apt-get update
  sudo apt-get install -y --no-install-recommends \
       git wget ca-certificates m4 \
       patch unzip libgtk2.0-dev \
       valac libgtksourceview2.0-dev \
       cmake build-essential
  
  cd /tmp
  dl_and_unzip_llvm-clang Linux ab42b50fd7fbd59254d3a8aef5473a5c6ceb9ca3508f31c76d95ee5d31268291
  dl_and_unzip_vfdeps https://vfdeps-cxx-linux.herokuapp.com/$VFDEPS_NAME-linux.txz c69e9bb1f058d827727d28922f3ebb6353f2fcbc8bd7dfe3ece54f94

  cd $script_dir/src/cxx_frontend/ast_exporter/build
  cmake -DLLVM_INSTALL_DIR=/tmp/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION -DVFDEPS=/tmp/$VFDEPS_NAME -DCMAKE_BUILD_TYPE=Release ..


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
  brewinstall cmake
  export PKG_CONFIG_PATH=/opt/X11/lib/pkgconfig
  sudo mkdir /usr/local/$VFDEPS_NAME
  sudo mkdir /usr/local/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION
  sudo chown -R $(whoami):admin /usr/local/*

  cd /usr/local
  dl_and_unzip_llvm-clang MacOS 365648cc3fea920b49dc262b13a19d64896d873c1ceaa40d3da37c71c8201168
  dl_and_unzip_vfdeps https://vfdeps-cxx-macos.herokuapp.com/$VFDEPS_NAME-macos.txz 301bf548e6bdbaac79ef49f3c2eb787a37b8487c4c25de1aec92b6c5

  cd $script_dir/src/cxx_frontend/ast_exporter/build
  cmake -DLLVM_INSTALL_DIR=/usr/local/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION -DVFDEPS=/usr/local/$VFDEPS_NAME -DCMAKE_BUILD_TYPE=Release ..
  
else
  echo "Your OS is not supported by this script."
  exit 1
  
fi