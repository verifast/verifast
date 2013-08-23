#
# Provides targets for printing pretty errors when a tool or library is
# necessary for another target but not found.
# For example, a target that needs the tool "ocamlbuild" will depend
# on the target "ocamlbuild", causing a pretty error if ocamlbuild
# is not found.
# This way, such an error is not displayed when the user is building
# a target that does not require the tool.
#

ifndef DEPENDENCYERRORS_MAKE_INCLUDED
  DEPENDENCYERRORS_MAKE_INCLUDED = yes

TOOLS = ocamlopt ocamlbuild make ocamlfind ocamlc
LIBS = lablgtk2 lablgtk2.sourceview2
$(TOOLS):
	which "$@" >/dev/null || echo "Install $@ first" ; which "$@" >/dev/null
.PHONY: $(TOOLS)

$(LIBS): ocamlfind
	ocamlfind query "$@" >/dev/null || echo "Install $@ first" ; ocamlfind query "$@" >/dev/null
.PHONY: $(LIBS)

endif

