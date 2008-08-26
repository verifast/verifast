verifast2.exe: proverapi.cmo redux.cmo z3prover.cmo verifast2.ml verifast2console.ml
	ocamlc -use-runtime $(Z3)\ocaml\z3run.exe -warn-error F -g -pp camlp4o -o verifast2.exe -I $(Z3)\ocaml unix.cma $(Z3)\ocaml\z3.cma proverapi.cmo redux.cmo z3prover.cmo verifast2.ml verifastPluginZ3.ml verifastPluginRedux.ml verifast2console.ml

proverapi.cmo: proverapi.ml
	ocamlc -warn-error F -g -c proverapi.ml

redux.cmo: proverapi.cmo redux.ml
	ocamlc -warn-error F -g -c proverapi.cmo redux.ml

z3prover.cmo: proverapi.cmo z3prover.ml
	ocamlc -warn-error F -g -c -I $(Z3)\ocaml z3prover.ml

verifast2.opt.exe: proverapi.cmx redux.cmx z3prover.cmx
	ocamlopt.opt -warn-error F -pp camlp4o -o verifast2.opt.exe -I $(Z3)\ocaml ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa z3.cmxa proverapi.cmx redux.cmx z3prover.cmx verifast2.ml verifastPluginZ3.ml verifastPluginRedux.ml verifast2Console.ml

proverapi.cmx: proverapi.ml
	ocamlopt.opt -warn-error F -c proverapi.ml

redux.cmx: proverapi.cmx redux.ml
	ocamlopt.opt -warn-error F -c proverapi.cmx redux.ml

z3prover.cmx: proverapi.cmx z3prover.ml
	ocamlopt.opt -warn-error F -c -I $(Z3)\ocaml z3.cmxa proverapi.cmx z3prover.ml

