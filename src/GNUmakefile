ifdef Z3
  Z3DEPS = z3prover.cmx verifastPluginZ3.ml
  Z3ARGS = -I $(Z3)/ocaml z3.cmxa z3prover.cmx verifastPluginZ3.ml -ccopt "-I$(Z3)/ocaml -L$(Z3)/bin -L$(Z3)/lib" -cclib -lz3-gmp -cclib -lz3stubs $(OCAMLLIB)/libcamlidl.a
else
  Z3DEPS =
  Z3ARGS =
endif

test: mysh verifast vfide dlsymtool
	export PATH=`pwd`:$PATH; cd ..; src/mysh < src/testsuite.mysh

dlsymtool: dlsymtool.ml
	ocamlopt.opt -o dlsymtool dlsymtool.ml

mysh: mysh.ml
	ocamlopt.opt -o mysh unix.cmxa mysh.ml

reduxtest: verifastredux.opt
	cd ../examples
	../src/verifastredux.opt linkedlist.c
	../src/verifastz3.opt linkedlist2.c
#	../src/verifastredux.opt composite.c
	../src/verifastredux.opt composite4.c
#	../src/verifastredux.opt sorted_bintree.c
	../src/verifastredux.opt -c iter.c
	cd java
#	../../src/verifastredux.opt -c Tree.java
#	../../src/verifastredux.opt -c Tree2.java
	cd ..
	cd chat
	../../src/verifastredux.opt -c stringBuffers.c
#	../../src/verifastredux.opt stringBuffers.c sockets.o threading.o lists.o -allow_assume chat.c
	cd ..
	cd chatbot
	../../src/verifastz3.opt -c bot.c
	cd ..

Printexc_proxy.cmx:
	cp Printexc_proxy_310.ml Printexc_proxy.ml
	ocamlopt -c Printexc_proxy.ml

ifdef MAC
Fonts.cmx: Fonts_mac.ml
	cp Fonts_mac.ml Fonts.ml
	ocamlopt -c Fonts.ml
else
Fonts.cmx: Fonts_default.ml
	cp Fonts_default.ml Fonts.ml
	ocamlopt -c Fonts.ml
endif

vfversion.cmi: vfversion.mli
	ocamlc -c vfversion.mli

vfversion_cmo: vfversion.cmi
	ocaml generate_vfversion.ml
	ocamlc -c vfversion.ml

vfversion_cmx: vfversion.cmi
	ocaml generate_vfversion.ml
	ocamlopt -c vfversion.ml

verifastRedux: vfversion_cmo proverapi.cmo simplex.cmo redux.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml
	ocamlc -warn-error F -w p -g -pp camlp4o -o verifastRedux unix.cma proverapi.cmo nums.cma simplex.cmo redux.cmo vfversion.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml

#verifast: vfversion_cmo proverapi.cmo simplex.cmo redux.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
#	ocamlc -custom -warn-error F -g -pp camlp4o -o verifast -I $(Z3)/ocaml unix.cma $(Z3)/ocaml/z3.cma proverapi.cmo nums.cma simplex.cmo redux.cmo z3prover.cmo vfversion.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifastZ3: vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o verifastZ3 -I $(Z3)/ocaml unix.cma nums.cma $(Z3)/ocaml/z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml $(Z3)/ocaml/z3_stubs.obj $(Z3)/bin/z3.lib $(OCAMLLIB)/libcamlidl.lib ole32.lib

vfideZ3: vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfide.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o vfideZ3 -I $(Z3)/ocaml -I +lablgtk2 lablgtk.cma gtkInit.cmo unix.cma nums.cma $(Z3)/ocaml/z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfide.ml $(Z3)/ocaml/z3_stubs.obj $(Z3)/bin/z3.lib $(OCAMLLIB)/libcamlidl.lib ole32.lib -ccopt "/link /LIBPATH:"$(GTKLIB)

mynum.cmx: mynum.ml
	ocamlopt.opt -c nums.cmxa mynum.ml

vfide: Printexc_proxy.cmx vfversion_cmx proverapi.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3DEPS) Fonts.cmx vfide.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o vfide -I +lablgtk2 lablgtk.cmxa gtkInit.cmx unix.cmxa nums.cmxa proverapi.cmx Printexc_proxy.cmx vfversion.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3ARGS) Fonts.cmx vfide.ml

vfideredux.opt: vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.cmx verifastPluginRedux.ml vfide.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o vfideredux.opt -I +lablgtk2 lablgtk.cmxa gtkInit.cmx unix.cmxa proverapi.cmx nums.cmxa simplex.cmx redux.cmx vfversion.cmx verifast.cmx verifastPluginRedux.ml vfide.ml

verifast.cmx: vfversion.cmi proverapi.cmx verifast.ml 
	ocamlopt.opt -warn-error F -pp camlp4o -c proverapi.cmx verifast.ml

verifast.cmo: vfversion.cmi proverapi.cmo verifast.ml
	ocamlc.opt -warn-error F -g -pp camlp4o -c verifast.ml

simplex.cmo: simplex.ml
	ocamlc -warn-error F -g -c simplex.ml

proverapi.cmo: proverapi.ml
	ocamlc -warn-error F -g -c proverapi.ml

redux.cmo: proverapi.cmo simplex.cmo redux.ml
	ocamlc -warn-error F -w p -g -c redux.ml

z3prover.cmo: proverapi.cmo z3prover.ml
	ocamlc -warn-error F -g -c -I $(Z3)/ocaml z3prover.ml

verifast.opt: vfversion_cmx proverapi.cmx redux.cmx z3prover.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifast.opt -I $(Z3)/ocaml ole32.lib $(OCAMLLIB)/libcamlidl.lib unix.cmxa z3.cmxa proverapi.cmx redux.cmx z3prover.cmx vfversion.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifast: vfversion_cmx proverapi.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3DEPS) vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifast unix.cmxa nums.cmxa proverapi.cmx vfversion.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3ARGS) vfconsole.ml

proverapi.cmx: proverapi.ml
	ocamlopt.opt -warn-error F -c proverapi.ml

simplex.cmx: simplex.ml
	ocamlopt.opt -warn-error F -c simplex.cmx simplex.ml

redux.cmx: proverapi.cmx simplex.cmx redux.ml
	ocamlopt.opt -warn-error F -c redux.ml

z3prover.cmx: proverapi.cmx z3prover.ml
	ocamlopt.opt -warn-error F -c -I $(Z3)/ocaml z3.cmxa proverapi.cmx z3prover.ml

verifastRedux.opt: vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifastRedux.opt unix.cmxa nums.cmxa proverapi.cmx simplex.cmx redux.cmx vfversion.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml

release: test
	mkdir verifast-$(VFVERSION)
	mkdir verifast-$(VFVERSION)/bin
ifdef Z3
	cp verifast verifast-$(VFVERSION)/bin/verifast-core
	cp vfide verifast-$(VFVERSION)/bin/vfide-core
	cp verifast.sh verifast-$(VFVERSION)/bin/verifast
	cp vfide.sh verifast-$(VFVERSION)/bin/vfide
	cp $(Z3)/lib/libz3-gmp.so verifast-$(VFVERSION)/bin
	cp ../Z3.LICENSE.txt verifast-$(VFVERSION)
else
	cp verifast verifast-$(VFVERSION)/bin
	cp vfide verifast-$(VFVERSION)/bin
endif
	cp assume.vfmanifest crt.vfmanifest prelude.h prelude_core.h stdlib.h stdio.h malloc.h string.h list.h verifast-$(VFVERSION)/bin
	cp -R rt verifast-$(VFVERSION)/bin
	cp -R ../examples verifast-$(VFVERSION)
	cp -R ../tests verifast-$(VFVERSION)
	cp -R ../tutorial verifast-$(VFVERSION)
	cp testsuite.mysh verifast-$(VFVERSION)
	cp ../test.sh verifast-$(VFVERSION)
	cp mysh verifast-$(VFVERSION)/bin
	cp dlsymtool verifast-$(VFVERSION)/bin
