
all: trivial_verifast_plugin.cmxs verify

OCAMLOPT ?= ocamlopt.opt

trivial_verifast_plugin.cmxs: DynType.mli plugins.mli plugins2.mli trivial_plugin.ml
	${OCAMLOPT} -w -8 -o trivial_verifast_plugin.cmxs -shared DynType.mli plugins.mli plugins2.mli trivial_plugin.ml

verify: trivial_verifast_plugin.cmxs
	verifast -c -allow_should_fail plugin.c

clean:
	-rm *.cmi *.cmx *.o *.cmxs
