#!/bin/bash

# Installs OCaml and lablgtk on Windows. Called by setup-windows.bat.

dl_and_unzip(){
  url="$1"
  filename=$(basename "$url")
  hash="$2"
  wget --progress=dot:mega -c "$url"
  echo "$hash *$filename" | sha1sum -c || exit 1
  7z -y x "$filename"
}



set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

cd /cygdrive/c

dl_and_unzip http://www.cs.kuleuven.be/~bartj/verifast/vfdeps-17.12-win32.zip 416bb30e96d5f54543fe53ef83a9b44f28cc1eb6

echo 'export PATH="/cygdrive/c/vfdeps-17.12/bin:$PATH"' >> ~/.bash_profile
      export PATH="/cygdrive/c/vfdeps-17.12/bin:$PATH"
