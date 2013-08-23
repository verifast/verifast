#
# Builds the vfide frontend.
#

ifndef VFIDE_MAKE_INCLUDED
  VFIDE_MAKE_INCLUDED = yes

include init.make
include vfcommon.make

ifeq ($(OS), linux)
  vfide: OCAMLBUILDFLAGS += -lib lablgtksourceview2
  vfide: OCAMLBUILD_SUBTARGETS += lablgtk2.sourceview2
endif

vfide: run_ocamlbuild_vfide
vfide: OCAMLBUILDFLAGS+=-use-ocamlfind -pkgs lablgtk2 -lib unix $(OCAMLBUILDFLAGS_VFCOMMON)
run_ocamlbuild_vfide: lablgtk2 ocamlfind run_ocamlbuild_vfcommon
vfide: BINNAME=vfide
vfide: SRCNAME=vfide.ml
vfide: INCLUDECODE+=$(INCLUDECODE_VFCOMMON)

.PHONY: .vfide

clean::
	rm -f $(BINDIR)/vfide$(DOTEXE)
#	Prevent cygwin/mingw to try launch an ELF executable:
	rm -f $(BINDIR)/vfide

endif

