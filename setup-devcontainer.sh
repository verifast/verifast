#!/bin/bash

set -e
set -x

./setup-build.sh

. ~/.cargo/env

# The toolchain for building VeriFast is installed by ./setup-build.sh (not using opam), but
# we now use opam to install ocaml-lsp-server.
sudo apt-get install -y --no-install-recommends opam
opam init --disable-sandboxing -y -n -c 4.14.0
opam repo add archive git+https://github.com/ocaml/opam-repository-archive
opam install -y dune.3.14.2 ocaml-lsp-server ocamlformat

WORKSPACEFOLDER=`pwd`
echo ". $WORKSPACEFOLDER/setenv.sh" >> ~/.bashrc

. ./setenv.sh
cd src && make build
