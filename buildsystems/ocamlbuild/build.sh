#!/bin/bash
error(){
	echo "$BUILDSCRIPTNAME: $1"
	exit 1
}

ORIGINALDIR="$PWD"
BUILDSCRIPTNAME="$(basename "$0")"
BUILDSCRIPTDIR="$(dirname "$(readlink -f "$0")")" || error "Cannot find my own dir!"
SRCDIR="$(readlink -e "$BUILDSCRIPTDIR/../../src/")" || error "Cannot find src/ dir!"
BINDIR="$(readlink -e "$BUILDSCRIPTDIR/../../bin/")" || error "Cannot find bin/ dir!"
BUILDDIR="$(readlink -m "$BUILDSCRIPTDIR/_ocamlbuild")"
mkdir -p "$BUILDDIR" || error "My build dir doesn't exist and I cannot create it!"
OCAMLOPT="$(which ocamlopt)" || error "Cannot find ocamlopt"

# Ocamlbuild gets confused when other buildsystems leave their garbage.
rm -f "$SRCDIR"/*.{cm*,o,a}

# I don't know how to compile .c files with ocamlbuild. So just do this the old-fashioned way.
make -C "$SRCDIR"/linux OCAMLOPTOPT="$OCAMLOPT"

cd "$SRCDIR/"
cat verifastPluginRedux.ml vfconsole.ml > buildthis.ml
if ocamlbuild -j 32 -pp camlp4o.opt -no-hygiene \
	-lflags -I,"$SRCDIR",-I,"$SRCDIR"/linux \
	-cflags -I,"$SRCDIR"/linux \
	-libs Perf,nums,dynlink \
	-build-dir "$BUILDDIR" \
	buildthis.native
then
	cp "$BUILDDIR"/buildthis.native "$BINDIR"/verifast
fi

rm -f buildthis.ml

cd "$ORIGINALDIR"


