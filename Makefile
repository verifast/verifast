verifast2.exe: proverapi.cmo redux.cmo z3prover.cmo verifast2.ml verifastPluginZ3.ml verifastPluginRedux.ml verifast2console.ml
	ocamlc -use-runtime $(Z3)\ocaml\z3run.exe -warn-error F -g -pp camlp4o -o verifast2.exe -I $(Z3)\ocaml unix.cma $(Z3)\ocaml\z3.cma proverapi.cmo redux.cmo z3prover.cmo verifast2.ml verifastPluginZ3.ml verifastPluginRedux.ml verifast2console.ml

verifastZ3.exe: proverapi.cmo z3prover.cmo verifast2.ml verifastPluginZ3.ml verifast2console.ml
	ocamlc -use-runtime $(Z3)\ocaml\z3run.exe -warn-error F -g -pp camlp4o -o verifastZ3.exe -I $(Z3)\ocaml unix.cma $(Z3)\ocaml\z3.cma proverapi.cmo z3prover.cmo verifast2.ml verifastPluginZ3.ml verifast2console.ml

vfideZ3.exe: proverapi.cmo z3prover.cmo verifast2.ml verifastPluginZ3.ml verifast2Ide.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o vfideZ3.exe -I $(Z3)\ocaml -I +lablgtk2 lablgtk.cma gtkInit.cmo unix.cma $(Z3)\ocaml\z3.cma proverapi.cmo z3prover.cmo verifast2.ml verifastPluginZ3.ml verifast2ide.ml $(Z3)\ocaml\z3_stubs.obj $(Z3)\bin\z3.lib $(OCAMLLIB)\libcamlidl.lib ole32.lib -ccopt "/link /LIBPATH:$(GTKLIB)"

proverapi.cmo: proverapi.ml
	ocamlc -warn-error F -g -c proverapi.ml

redux.cmo: proverapi.cmo redux.ml
	ocamlc -warn-error F -g -c proverapi.cmo redux.ml

z3prover.cmo: proverapi.cmo z3prover.ml
	ocamlc -warn-error F -g -c -I $(Z3)\ocaml z3prover.ml

verifast2.opt.exe: proverapi.cmx redux.cmx z3prover.cmx verifast2.ml verifastPluginZ3.ml verifastPluginRedux.ml verifast2Console.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifast2.opt.exe -I $(Z3)\ocaml ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa z3.cmxa proverapi.cmx redux.cmx z3prover.cmx verifast2.ml verifastPluginZ3.ml verifastPluginRedux.ml verifast2Console.ml

verifastz3.opt.exe: proverapi.cmx z3prover.cmx verifast2.ml verifastPluginZ3.ml verifast2Console.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifastz3.opt.exe -I $(Z3)\ocaml ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa z3.cmxa proverapi.cmx z3prover.cmx verifast2.ml verifastPluginZ3.ml verifast2Console.ml

proverapi.cmx: proverapi.ml
	ocamlopt.opt -warn-error F -c proverapi.ml

redux.cmx: proverapi.cmx redux.ml
	ocamlopt.opt -warn-error F -c proverapi.cmx redux.ml

z3prover.cmx: proverapi.cmx z3prover.ml
	ocamlopt.opt -warn-error F -c -I $(Z3)\ocaml z3.cmxa proverapi.cmx z3prover.ml

verifastRedux.opt.exe: proverapi.cmx redux.cmx verifast2.ml verifastPluginRedux.ml verifast2Console.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifastRedux.opt.exe unix.cmxa proverapi.cmx redux.cmx verifast2.ml verifastPluginRedux.ml verifast2Console.ml
