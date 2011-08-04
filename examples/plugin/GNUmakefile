all: trivial_verifast_plugin.cmxs verify

trivial_verifast_plugin.cmxs: DynType.mli plugins.mli plugins2.mli trivial_plugin.ml
	ocamlopt.opt -o trivial_verifast_plugin.cmxs -shared DynType.mli plugins.mli plugins2.mli trivial_plugin.ml

verify:
	verifast -c -allow_should_fail plugin.c

clean:
	rm *.cmi *.cmx *.o *.cmxs
