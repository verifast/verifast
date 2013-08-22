ifndef VFIDE_MAKE_INCLUDED
  VFIDE_MAKE_INCLUDED = yes

include init.make

ifeq ($(OS), linux)
  vfide: OCAMLBUILDFLAGS += -lib lablgtksourceview2
  run_ocamlbuild_vfide: lablgtk2.sourceview2
endif

vfide: OCAMLBUILDFLAGS+=-use-ocamlfind -pkgs lablgtk2 -lib unix
vfide: run_ocamlbuild_vfide
run_ocamlbuild_vfide: lablgtk2
vfide: BINNAME=vfide
vfide: SRCNAME=vfide.ml
vfide: INCLUDECODE+=$(SRCDIR)/verifastPluginRedux.ml
.PHONY: .vfide
OCAMLBUILDSUBTARGETS+=vfide

clean::
	rm -f $(BINDIR)/vfide

endif

