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
  if [ ! -e "verifast-downloads/$filename" ]; then
    wget -P verifast-downloads --progress=dot:mega -c "$url"
    echo "$hash *verifast-downloads/$filename" | sha"$sha"sum -c || exit 1
  else
    echo "Skipped downloading C:/verifast-downloads/$filename; file already exists"
  fi
  entry="$(tar t"$filter"f "verifast-downloads/$filename" | head -n 1)"
  if [ ! -e $entry ]; then
    tar x"$filter"f "verifast-downloads/$filename"
  else
    echo "Skipped extracting C:/verifast-downloads/$filename; file C:/$entry already exists"
  fi
}

script_dir=$(pwd)

cd /cygdrive/c
dl_and_unzip https://github.com/verifast/vf-llvm-clang-build/releases/download/v2.0.4/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION-Windows-MinGW-x86_64.tar.gz B6FF69088BF31A5C8B01B9D717B724CBC0A1362243C852FCBACBC0F58AC4F378 256 z
dl_and_unzip https://github.com/verifast/vfdeps-win/releases/download/23.04/vfdeps-e62a07d-win.txz 63a593c235fbcb4d86c4cbe821aca1a943873daadfbbc1af37f0bb3f 224 j

PATHCMD='export PATH="/cygdrive/c/vfdeps/bin:$PATH"'
if ! rustup show home; then
  if [ ! -e "verifast-downloads/rustup-init.exe" ]; then
    wget -O verifast-downloads/rustup-init.exe --progress=dot:mega https://win.rustup.rs/x86_64
  fi
  verifast-downloads/rustup-init.exe -y
  PATHCMD="$PATHCMD:"'"'"`cygpath -u $USERPROFILE/.cargo/bin`"'"'
fi

cd $script_dir/src/cxx_frontend/ast_exporter
cmake -S . -B build -G Ninja -DCMAKE_SYSTEM_NAME=Windows -DCMAKE_C_COMPILER=x86_64-w64-mingw32-gcc -DCMAKE_CXX_COMPILER=x86_64-w64-mingw32-g++ -DCMAKE_BUILD_TYPE=Release -DLLVM_INSTALL_DIR=/cygdrive/c/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION -DVFDEPS=/cygdrive/c/vfdeps

echo "$PATHCMD" >> ~/.bash_profile
eval "$PATHCMD"
