#!/bin/bash

#
# Installs dependencies, builds VeriFast, and runs tests.
# Suitable for home use and for continuous integration.
#
# Supported: vfide
# Not supported: z3
#

set -e # Stop as soon as a command fails.
set -x # Print what is being executed.

if [ $(uname -s) = "Linux" ]; then
  # Note: without gtksourceview2.0-dev, opam builds lablgtk builds with
  # sourceview bindings missing
  sudo apt-get install -y --no-install-recommends wget ca-certificates make m4 \
    gcc patch unzip libgtk2.0-dev valac gtksourceview2.0-dev
    
elif [ $(uname -s) = "Darwin" ]; then
  brew update
  brew install gtk+ gtksourceview vala
  export PKG_CONFIG_PATH=/opt/X11/lib/pkgconfig
  
else
  echo "Your OS is not supported by this script."
  exit 1
  
fi

# Install opam
mkdir -p ~/.local/bin && wget https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh -O - | sh -s ~/.local/bin

# Configure opam
export PATH=$PATH:~/.local/bin && eval `opam config env`

# Initialize opam
opam init -y --comp=4.02.1

# Install ocaml prerequisites
opam install -y core lablgtk camlidl

# Now build VeriFast and run tests
cd src && make -j 2

