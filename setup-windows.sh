#!/bin/bash

# Installs OCaml and lablgtk on Windows. Called by setup-windows.bat.

dl_and_unzip(){
  url="$1"
  filename=$(basename "$url")
  hash="$2"
  wget --progress=dot:mega -c "$url"
  echo "$hash *$filename" | sha1sum -c || exit 1
  tar xjf "$filename"
}



set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

cd /cygdrive/c

dl_and_unzip https://dl.bintray.com/verifast/verifast/vfdeps-649a3d5-win.txz 067fdf4e6fc69458bd651c0ea87a97bd96058262

echo 'export PATH="/cygdrive/c/vfdeps/bin:$PATH"' >> ~/.bash_profile
      export PATH="/cygdrive/c/vfdeps/bin:$PATH"
