#
# Internal configuration.
#
# You're not supposed to put your config in here. If you install
# your stuff properly, everything is autodetected. If you did not
# install properly, the solution is to install properly, not to mess
# up the build system :)
#
# i.e. this is config for the developers of the buildsystem,
# not for the user of the buildsystem!
#


ifndef INTERNALCONFIG_MAKE_INCLUDED
  INTERNALCONFIG_MAKE_INCLUDED = yes

-include settings.make

BUILDSCRIPTDIR := $(CURDIR)
SRCDIR    := $(BUILDSCRIPTDIR)/../../src
BINDIR    := $(BUILDSCRIPTDIR)/../../bin
BUILDDIR  := $(BUILDSCRIPTDIR)/_tempbuildfiles

OCAMLOPT  ?= ocamlopt
OCAMLC    ?= ocamlc
OCAMLBUILD?= ocamlbuild
OCAMLLIB  ?= $(shell ${OCAMLC} -where)
OCAML     ?= ocaml

ifndef VERBOSE
  # makes make not print the commands it executes.
  # This does not really belong to "internalconfig.make" but it does not belong anywhere else either...
  .SILENT:
endif

endif
