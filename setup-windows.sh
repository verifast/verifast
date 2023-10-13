#!/bin/bash

# Installs OCaml and lablgtk on Windows. Called by setup-windows.bat.

set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

. ./config.sh

dl_and_unzip() {
  url="$1"
  filename=$(basename "$url")
  hash="$2"
  sha="$3"
  filter="$4"
  wget -P verifast-downloads --progress=dot:mega -c "$url"
  echo "$hash *verifast-downloads/$filename" | sha"$sha"sum -c || exit 1
  tar x"$filter"f "verifast-downloads/$filename"
}

script_dir=$(pwd)

cd /cygdrive/c
dl_and_unzip https://github.com/NielsMommen/vf-llvm-clang-build/releases/download/v2.0.3/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION-Windows-MinGW-x86_64.tar.gz 0379947ECC2F475ECA7A876C858910DEAE507C2588BC8534935AE76C233AA49F 256 z
dl_and_unzip https://github.com/verifast/vfdeps-win/releases/download/23.04/vfdeps-e62a07d-win.txz 63a593c235fbcb4d86c4cbe821aca1a943873daadfbbc1af37f0bb3f 224 j

cd $script_dir/src/cxx_frontend/ast_exporter
cmake -S . -B build -G Ninja -DCMAKE_SYSTEM_NAME=Windows -DCMAKE_C_COMPILER=x86_64-w64-mingw32-gcc -DCMAKE_CXX_COMPILER=x86_64-w64-mingw32-g++ -DCMAKE_BUILD_TYPE=Release -DLLVM_INSTALL_DIR=/cygdrive/c/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION -DVFDEPS=/cygdrive/c/vfdeps

echo 'export PATH="/cygdrive/c/vfdeps/bin:$PATH"' >> ~/.bash_profile
      export PATH="/cygdrive/c/vfdeps/bin:$PATH"
