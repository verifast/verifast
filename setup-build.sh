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
  sudo tar "x"$filter"f" "/tmp/$filename"
}

dl_and_unzip_vfdeps() {
  url="$1"
  hash="$2"
  dl_and_unzip $url $hash 256 j
}

dl_and_unzip_llvm-clang() {
  platform="$1"
  hash="$2"
  dl_and_unzip "https://github.com/verifast/vf-llvm-clang-build/releases/download/v2.0.5/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION-$platform.tar.gz" $hash 256 z
}

script_dir=$(pwd)

if [ $(uname -s) = "Linux" ]; then
  sudo apt-get update
  sudo apt-get install -y --no-install-recommends \
       git wget ca-certificates m4 \
       patch unzip libgtk2.0-dev \
       valac \
       cmake build-essential ninja-build
  if ! sudo apt-get install -y --no-install-recommends libgtksourceview2.0-dev; then
    # libgtksourceview2.0-dev is not in recent Ubuntu releases, so add focal (20.04 LTS) repo
    sudo add-apt-repository "deb http://mirrors.kernel.org/ubuntu/ focal universe"
    sudo apt-get update
    sudo apt-get install -y --no-install-recommends libgtksourceview2.0-dev
  fi

  if ! rustup show home; then
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s - -y
  fi

  cd /
  dl_and_unzip_llvm-clang Linux 835a0da7ae9b237844d5dc9f3aa69cf76df08c7fa07dd1834850fd69c114011e
  dl_and_unzip_vfdeps https://github.com/verifast/vfdeps/releases/download/25.01/$VFDEPS_NAME-linux.txz 8d022c93d51a1d13ec1e782d767c60462405f6865d5ee416f82d6234e93ee580
  . "$script_dir/install-vfdeps.sh"

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
  if [ "$(uname -p)" = arm ]; then
    oras pull ghcr.io/homebrew/core/gtksourceview:2.10.5_7@sha256:0511545c79d16ff872f2bbc931abcdd5c1b4f3d70b71064f7d59989f68c8c073
    brew install ./gtksourceview--2.10.5_7.arm64_monterey.bottle.tar.gz
  else
    oras pull ghcr.io/homebrew/core/gtksourceview:2.10.5_7@sha256:368413983346081e277782a5df7ac4b9e9ad1adce149fa7028fa6d99e809b7ae
    brew install ./gtksourceview--2.10.5_7.monterey.bottle.tar.gz
  fi
  brewinstall vala
  brewinstall cmake
  brewinstall ninja
  export PKG_CONFIG_PATH=/opt/X11/lib/pkgconfig
  sudo mkdir /usr/local/$VFDEPS_NAME
  sudo mkdir /usr/local/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION

  if ! rustup show home; then
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s - -y
  fi

  cd /usr/local
  if [ "$(uname -p)" = arm ]; then
    dl_and_unzip_llvm-clang MacOS-aarch64 e56dee8f06c1bef9ee22f8d70b0ef4b4ddb9bca2590c706afa553bbfd72d3d49
    dl_and_unzip_vfdeps https://github.com/verifast/vfdeps/releases/download/25.01/$VFDEPS_NAME-macos-aarch64.txz 8bd48b02aa1887321d28b8490fe5803ea045845324f5d2adf49e72ddb6643bc1
  else
    dl_and_unzip_llvm-clang MacOS ceec6ba6f1b5694fae15b28bf20b33e08dbd6dce11fefe954a5659eb7ba32156
    dl_and_unzip_vfdeps https://github.com/verifast/vfdeps/releases/download/25.01/$VFDEPS_NAME-macos.txz 99d9eceb2f4e483a61d84015db5251c99d4ce3932535b4b4e4d37a23d0a0146d
  fi

  cd $script_dir/src/cxx_frontend/ast_exporter
  cmake -S . -B build -G Ninja -DLLVM_INSTALL_DIR=/usr/local/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION -DVFDEPS=/usr/local/$VFDEPS_NAME -DCMAKE_BUILD_TYPE=Release
  
else
  echo "Your OS is not supported by this script."
  exit 1
  
fi
