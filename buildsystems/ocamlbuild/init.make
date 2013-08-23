#
# Basic initialization that every other make file needs.
# Mainly to prevent having to write multiple includes in front of
# every makefile.
# Also some named-constant definition to avoid magic-constants/modifiability-issues.
#

ifndef INIT_MAKE_INCLUDED
  INIT_MAKE_INCLUDED = yes

OCAMLOPT  ?= ocamlopt
OCAMLC    ?= ocamlc
OCAMLBUILD?= ocamlbuild
OCAMLLIB  ?= $(shell ${OCAMLC} -where)

include internalconfig.make
include osdetect.make
include config.make
include dependencyerrors.make

endif
