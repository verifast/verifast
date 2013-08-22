ifndef INIT_MAKE_INCLUDED
  INIT_MAKE_INCLUDED = yes

OCAMLOPT  ?= ocamlopt
OCAMLBUILD?= ocamlbuild

TOOLS = ocamlopt ocamlbuild make ocamlfind
LIBS = lablgtk2 lablgtk2.sourceview2
$(TOOLS):
	which "$@" >/dev/null || echo "Install $@ first" ; which "$@" >/dev/null
.PHONY: $(TOOLS)

$(LIBS): ocamlfind
	ocamlfind query "$@" >/dev/null || echo "Install $@ first" ; ocamlfind query "$@" >/dev/null
.PHONY: $(LIBS)

include config.make
include osdetect.make
include debugconfig.make

endif
