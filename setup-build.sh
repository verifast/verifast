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
  dl_and_unzip "https://github.com/NielsMommen/vf-llvm-clang-build/releases/download/v2.0.3/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION-$platform.tar.gz" $hash 256 z
}

script_dir=$(pwd)

if [ $(uname -s) = "Linux" ]; then
  sudo apt-get update
  sudo apt-get install -y --no-install-recommends \
       git wget ca-certificates m4 \
       patch unzip libgtk2.0-dev \
       valac \
       cmake build-essential ninja-build
  if ! sudo apt-get install libgtksourceview2.0-dev; then
    # libgtksourceview2.0-dev is not in recent Ubuntu releases, so add focal (20.04 LTS) repo
    sudo add-apt-repository "deb http://mirrors.kernel.org/ubuntu/ focal universe"
    sudo apt-get update
    sudo apt-get install libgtksourceview2.0-dev
  fi

  if ! rustup show home; then
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s - -y
  fi

  cd /tmp
  dl_and_unzip_llvm-clang Linux f39cc6feb96ebbc5cf7cb39f304b3bf7484a32842da4859441da6f983c43f22a
  dl_and_unzip_vfdeps https://github.com/verifast/vfdeps/releases/download/23.04/$VFDEPS_NAME-linux.txz 9d108282a8a94526f8d043c3e2e4c3cac513788a42fa8d6964ee4937

  cd $script_dir/src/cxx_frontend/ast_exporter
  cmake -S . -B build -G Ninja -DLLVM_INSTALL_DIR=/tmp/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION -DVFDEPS=/tmp/$VFDEPS_NAME -DCMAKE_BUILD_TYPE=Release


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
  # brewinstall gtksourceview
  brewinstall oras
  oras pull ghcr.io/homebrew/core/gtksourceview:2.10.5_7@sha256:368413983346081e277782a5df7ac4b9e9ad1adce149fa7028fa6d99e809b7ae
  brew install ./gtksourceview--2.10.5_7.monterey.bottle.tar.gz
  brewinstall vala
  brewinstall cmake
  brewinstall ninja
  export PKG_CONFIG_PATH=/opt/X11/lib/pkgconfig
  sudo mkdir /usr/local/$VFDEPS_NAME
  sudo mkdir /usr/local/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION
  sudo chown -R $(whoami):admin /usr/local/*

  if ! rustup show home; then
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s - -y
  fi

  cd /usr/local
  dl_and_unzip_llvm-clang MacOS 77474d414aa7ddc4e68bc00525a8dccec284c9936c45f6241157070dc5dfdfd6
  dl_and_unzip_vfdeps https://github.com/verifast/vfdeps/releases/download/23.04/$VFDEPS_NAME-macos.txz a43ad92202761103a03400d78679a94838eaad44567c69b94eedd10d

  cd $script_dir/src/cxx_frontend/ast_exporter
  cmake -S . -B build -G Ninja -DLLVM_INSTALL_DIR=/usr/local/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION -DVFDEPS=/usr/local/$VFDEPS_NAME -DCMAKE_BUILD_TYPE=Release
  
else
  echo "Your OS is not supported by this script."
  exit 1
  
fi
