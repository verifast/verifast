#!/bin/bash

#
# Installs dependencies, builds VeriFast, and runs tests.
# Suitable for home use and for continuous integration.
#

set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

. ./config.sh

VF_LLVM_CLANG_BUILD_NAME=vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION

dl_and_unzip() {
  url="$1"
  filename=$(basename "$url")
  hash="$2"
  sha="$3"
  filter="$4"
  name="$5"
  if [ -e "$name" -a -n "$(ls -A $name)" ]; then
    echo "dl_and_unzip: skipping $name; the directory already exists and is nonempty"
  else
    if [ -e "/tmp/$filename" ]; then
      echo "dl_and_unzip: skipping download of $name; downloaded file /tmp/$filename already exists"
    else
      curl -Lf -o "/tmp/$filename" "$url"
      echo "$hash  /tmp/$filename" | shasum -a "$sha" -c || exit 1
    fi
    if [ ! -e "$name" -a "$(pwd)" = "/usr/local" ]; then
      sudo mkdir "$name"
      sudo chown -R $(whoami):admin "$name"
    fi
    tar "x"$filter"f" "/tmp/$filename"
  fi
}

dl_and_unzip_vfdeps() {
  url="$1"
  hash="$2"
  dl_and_unzip $url $hash 224 j $VFDEPS_NAME
}

dl_and_unzip_llvm-clang() {
  platform="$1"
  hash="$2"
  dl_and_unzip "https://github.com/NielsMommen/vf-llvm-clang-build/releases/download/v2.0.3/$VF_LLVM_CLANG_BUILD_NAME-$platform.tar.gz" $hash 256 z $VF_LLVM_CLANG_BUILD_NAME
}

script_dir=$(pwd)

if [ $(uname -s) = "Linux" ]; then
  sudo apt-get update
  sudo apt-get install -y --no-install-recommends \
       git wget ca-certificates m4 \
       patch unzip libgtk2.0-dev \
       valac libgtksourceview2.0-dev \
       cmake build-essential ninja-build

  if ! rustup show home; then
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s - -y
  fi

  cd /tmp
  dl_and_unzip_llvm-clang Linux f39cc6feb96ebbc5cf7cb39f304b3bf7484a32842da4859441da6f983c43f22a
  dl_and_unzip_vfdeps https://github.com/verifast/vfdeps/releases/download/23.04/$VFDEPS_NAME-linux.txz 9d108282a8a94526f8d043c3e2e4c3cac513788a42fa8d6964ee4937

  cd $script_dir/src/cxx_frontend/ast_exporter
  cmake -S . -B build -G Ninja -DLLVM_INSTALL_DIR=/tmp/$VF_LLVM_CLANG_BUILD_NAME -DVFDEPS=/tmp/$VFDEPS_NAME -DCMAKE_BUILD_TYPE=Release


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
  brewinstall ninja
  export PKG_CONFIG_PATH=/opt/X11/lib/pkgconfig

  if ! rustup show home; then
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s - -y
  fi

  cd /usr/local
  dl_and_unzip_llvm-clang MacOS 77474d414aa7ddc4e68bc00525a8dccec284c9936c45f6241157070dc5dfdfd6
  dl_and_unzip_vfdeps https://github.com/verifast/vfdeps/releases/download/23.04/$VFDEPS_NAME-macos.txz a43ad92202761103a03400d78679a94838eaad44567c69b94eedd10d

  cd $script_dir/src/cxx_frontend/ast_exporter
  cmake -S . -B build -G Ninja -DLLVM_INSTALL_DIR=/usr/local/$VF_LLVM_CLANG_BUILD_NAME -DVFDEPS=/usr/local/$VFDEPS_NAME -DCMAKE_BUILD_TYPE=Release
  
else
  echo "Your OS is not supported by this script."
  exit 1
  
fi
