#!/bin/bash

# Installs OCaml and lablgtk on Windows. Called by setup-windows.bat.

dl_and_unzip(){
  url="$1"
  filename=$(basename "$url")
  hash="$2"
  wget --progress=dot:mega -c "$url"
  echo "$hash *$filename" | sha224sum -c || exit 1
  tar xjf "$filename"
}

set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

script_dir=$(pwd)
MSVC_CACHE_FILEPATH=$script_dir/src/cxx_frontend/ast_exporter/MSVC_CACHE

cd /cygdrive/c
wget --progress=dot:mega -c https://github.com/NielsMommen/vf-llvm-clang-build/releases/download/v1.0.0/llvm-clang_windows-latest.tar.gz
tar xzf llvm-clang_windows-latest.tar.gz

dl_and_unzip https://vfdeps-cxx-win.herokuapp.com/vfdeps-e4c714b-win.txz 95d0d51436ac2042227013f61f72a2503774b2fe944b2cadaccd3eb5

cd $script_dir/src/cxx_frontend/ast_exporter
# $VCINSTALLDIR and $VCToolsRedistDir are set by invoking vcvarsall.bat in setup-windows.bat
echo VCVARSALL_BAT_DIR="\"$VCINSTALLDIR\Auxiliary\Build\"" > $MSVC_CACHE_FILEPATH
echo MSVC_REDIST_DIR="\"$VCToolsRedistDir\x86\Microsoft.VC142.CRT\"" >> $MSVC_CACHE_FILEPATH

cd build
cmd /C "cmake -DLLVM_INSTALL_DIR=C:/llvm-clang_windows-latest -DVFDEPS=C:/vfdeps -A Win32 -Thost=x64 .."

echo 'export PATH="/cygdrive/c/vfdeps/bin:$PATH"' >> ~/.bash_profile
      export PATH="/cygdrive/c/vfdeps/bin:$PATH"
