#
# Configuration for the user of the buildsystem.
#

ifndef CONFIG_MAKE_INCLUDED
  CONFIG_MAKE_INCLUDED = yes

ifdef VERBOSE
  # makes ocamlbuild print the commands it executes
  OCAMLBUILDFLAGS+=-classic-display
endif

ifndef VERBOSE
  # makes make not print the commands it executes
  .SILENT:
endif

# All warnings are errors, except a few that we hide.
OCAMLBUILDFLAGS+= -cflags -warn-error,A,-w,-8,-w,-28,-w,-26,-w,-10


endif
