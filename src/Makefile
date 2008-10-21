verifastRedux.exe: proverapi.cmo simplex.cmo redux.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml
	ocamlc -warn-error F -w p -g -pp camlp4o -o verifastRedux.exe unix.cma proverapi.cmo nums.cma simplex.cmo redux.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml

verifast.exe: proverapi.cmo simplex.cmo redux.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o verifast.exe -I $(Z3)\ocaml unix.cma $(Z3)\ocaml\z3.cma proverapi.cmo nums.cma simplex.cmo redux.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifastZ3.exe: proverapi.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml vfconsole.ml
	ocamlc -use-runtime $(Z3)\ocaml\z3run.exe -warn-error F -g -pp camlp4o -o verifastZ3.exe -I $(Z3)\ocaml unix.cma $(Z3)\ocaml\z3.cma proverapi.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml vfconsole.ml

vfideZ3.exe: proverapi.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml vfide.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o vfideZ3.exe -I $(Z3)\ocaml -I +lablgtk2 lablgtk.cma gtkInit.cmo unix.cma $(Z3)\ocaml\z3.cma proverapi.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml vfide.ml $(Z3)\ocaml\z3_stubs.obj $(Z3)\bin\z3.lib $(OCAMLLIB)\libcamlidl.lib ole32.lib -ccopt "/link /LIBPATH:$(GTKLIB)"

vfideZ3.opt.exe: proverapi.cmx z3prover.cmx verifast.cmx verifastPluginZ3.ml vfide.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o vfidez3.opt.exe -I $(Z3)\ocaml -I +lablgtk2 lablgtk.cmxa gtkInit.cmx ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa nums.cmxa z3.cmxa proverapi.cmx z3prover.cmx verifast.cmx verifastPluginZ3.ml vfide.ml -ccopt "/link /LIBPATH:$(GTKLIB)"

vfideredux.opt.exe: proverapi.cmx simplex.cmx redux.cmx verifast.cmx verifastPluginRedux.ml vfide.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o vfideredux.opt.exe -I +lablgtk2 lablgtk.cmxa gtkInit.cmx unix.cmxa proverapi.cmx nums.cmxa simplex.cmx redux.cmx verifast.cmx verifastPluginRedux.ml vfide.ml -ccopt "/link /LIBPATH:$(GTKLIB)"

verifast.cmx: proverapi.cmx verifast.ml 
	ocamlopt.opt -warn-error F -pp camlp4o -c proverapi.cmx verifast.ml

simplex.cmo: simplex.ml
	ocamlc -warn-error F -g -c simplex.ml

proverapi.cmo: proverapi.ml
	ocamlc -warn-error F -g -c proverapi.ml

redux.cmo: proverapi.cmo simplex.cmo redux.ml
	ocamlc -warn-error F -w p -g -c redux.ml

z3prover.cmo: proverapi.cmo z3prover.ml
	ocamlc -warn-error F -g -c -I $(Z3)\ocaml z3prover.ml

verifast.opt.exe: proverapi.cmx redux.cmx z3prover.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifast.opt.exe -I $(Z3)\ocaml ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa z3.cmxa proverapi.cmx redux.cmx z3prover.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifastz3.opt.exe: proverapi.cmx z3prover.cmx verifast.ml verifastPluginZ3.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifastz3.opt.exe -I $(Z3)\ocaml ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa nums.cmxa z3.cmxa proverapi.cmx z3prover.cmx verifast.ml verifastPluginZ3.ml vfconsole.ml

proverapi.cmx: proverapi.ml
	ocamlopt.opt -warn-error F -c proverapi.ml

simplex.cmx: simplex.ml
	ocamlopt.opt -warn-error F -c simplex.cmx simplex.ml

redux.cmx: proverapi.cmx simplex.cmx redux.ml
	ocamlopt.opt -warn-error F -c redux.ml

z3prover.cmx: proverapi.cmx z3prover.ml
	ocamlopt.opt -warn-error F -c -I $(Z3)\ocaml z3.cmxa proverapi.cmx z3prover.ml

verifastRedux.opt.exe: proverapi.cmx simplex.cmx redux.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifastRedux.opt.exe unix.cmxa nums.cmxa proverapi.cmx simplex.cmx redux.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml
