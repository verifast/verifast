ifdef Z3
  Z3DEPS = z3prover.cmx verifastPluginZ3.ml
  Z3ARGS = -I $(Z3)/ocaml z3.cmxa z3prover.cmx verifastPluginZ3.ml -ccopt "-I$(Z3)/ocaml -L$(Z3)/bin -L$(Z3)/lib" -cclib -lz3-gmp -cclib -lz3stubs $(OCAMLLIB)/libcamlidl.a
  GTKSOURCEVIEW = lablgtksourceview2.cmxa
  GTKSOURCEVIEW_DEPS =
else
  Z3DEPS =
  Z3ARGS =
  GTKSOURCEVIEW = -I macos GSourceView2.cmx
  GTKSOURCEVIEW_DEPS = macos/GSourceView2.cmx
endif

ifdef MAC
  numcpu := $(shell sysctl -n hw.ncpu)
else
  # Also works under cygwin (tested).
  numcpu := $(shell cat /proc/cpuinfo | grep 'processor' | wc -l)
endif

test: ../bin/mysh ../bin/verifast ../bin/vfide ../bin/dlsymtool ../bin/vfstrip ../bin/list.vfmanifest ../bin/raw_ghost_lists.vfmanifest ../bin/listex.vfmanifest
	export PATH=`pwd`:$$PATH; cd ..; bin/mysh -cpus $(numcpu) < testsuite.mysh

../bin/list.vfmanifest: ../bin/list.c ../bin/list.h
	cd ../bin; verifast -c -emit_vfmanifest list.c

../bin/listex.vfmanifest: ../bin/listex.c ../bin/listex.h
	cd ../bin; verifast -c -emit_vfmanifest listex.c

../bin/raw_ghost_lists.vfmanifest: ../bin/raw_ghost_lists.c ../bin/raw_ghost_lists.h
	cd ../bin; verifast -c -emit_vfmanifest raw_ghost_lists.c

../bin/vfstrip: vfstrip.ml
	ocamlopt.opt -o ../bin/vfstrip vfstrip.ml

../bin/dlsymtool: dlsymtool.ml
	ocamlopt.opt -o ../bin/dlsymtool dlsymtool.ml

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

../bin/mysh: Fonts.cmx mysh.ml
	ocamlopt.opt -thread -o ../bin/mysh unix.cmxa threads.cmxa Fonts.cmx mysh.ml

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

ifdef Z3
else
macos/GSourceView2.cmx: macos/GSourceView2.ml
	cd macos; ocamlopt.opt -c -I +lablgtk2 GSourceView2.ml
endif

../bin/vfide: Printexc_proxy.cmx vfversion_cmx proverapi.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3DEPS) Fonts.cmx $(GTKSOURCEVIEW_DEPS) vfide.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o ../bin/vfide -I +lablgtk2 lablgtk.cmxa $(GTKSOURCEVIEW) gtkInit.cmx unix.cmxa nums.cmxa -I ./linux Perf.cmx proverapi.cmx Printexc_proxy.cmx vfversion.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3ARGS) Fonts.cmx vfide.ml

vfideredux.opt: vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.cmx verifastPluginRedux.ml vfide.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o vfideredux.opt -I +lablgtk2 lablgtk.cmxa gtkInit.cmx unix.cmxa proverapi.cmx nums.cmxa simplex.cmx redux.cmx vfversion.cmx verifast.cmx verifastPluginRedux.ml vfide.ml

linux/Perf.cmx: linux/Perf.ml
	cd linux; ocamlopt.opt -c Perf.ml

verifast.cmx: linux/Perf.cmx vfversion.cmi proverapi.cmx verifast.ml 
	ocamlopt.opt -warn-error F -pp camlp4o -c -I ./linux Perf.cmx proverapi.cmx verifast.ml

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

SExpressions.cmi: SExpressions.mli
	ocamlopt.opt -c SExpressions.mli

SExpressions.cmx: SExpressions.cmi SExpressions.ml
	ocamlopt.opt -c nums.cmxa SExpressions.ml

SExpressionEmitter.cmi: verifast.cmx SExpressionEmitter.mli
	ocamlopt.opt -c SExpressionEmitter.mli

SExpressionEmitter.cmx: verifast.cmx SExpressionEmitter.cmi SExpressions.cmx SExpressionEmitter.ml
	ocamlopt.opt -c nums.cmxa SExpressionEmitter.ml

../bin/verifast: vfversion_cmx proverapi.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3DEPS) SExpressions.cmx SExpressionEmitter.cmx vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o ../bin/verifast unix.cmxa nums.cmxa -I ./linux Perf.cmx proverapi.cmx vfversion.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3ARGS) SExpressions.cmx SExpressionEmitter.cmx vfconsole.ml

proverapi.cmx: proverapi.ml
	ocamlopt.opt -warn-error F -c proverapi.ml

simplex.cmx: simplex.ml
	ocamlopt.opt -warn-error F -c simplex.cmx simplex.ml

redux.cmx: proverapi.cmx simplex.cmx redux.ml
	ocamlopt.opt -warn-error F -c redux.ml

z3prover.cmx: linux/Perf.cmx proverapi.cmx z3prover.ml
	ocamlopt.opt -warn-error F -c -I $(Z3)/ocaml z3.cmxa -I ./linux Perf.cmx proverapi.cmx z3prover.ml

verifastRedux.opt: vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifastRedux.opt unix.cmxa nums.cmxa proverapi.cmx simplex.cmx redux.cmx vfversion.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml

release: test release_core

release_core:
	mkdir verifast-$(VFVERSION)
	cp -R ../bin verifast-$(VFVERSION)
ifdef Z3
	cd verifast-$(VFVERSION)/bin; mv verifast verifast-core
	cd verifast-$(VFVERSION)/bin; mv vfide vfide-core
	cp verifast.sh verifast-$(VFVERSION)/bin/verifast
	cp vfide.sh verifast-$(VFVERSION)/bin/vfide
	cp $(Z3)/lib/libz3-gmp.so verifast-$(VFVERSION)/bin
	cp /usr/lib/libgtksourceview-2.0.so.0.0.0 verifast-$(VFVERSION)/bin/libgtksourceview-2.0.so.0
	cp ../Z3.LICENSE.txt verifast-$(VFVERSION)
else
	cd verifast-$(VFVERSION)/bin; mv vfide vfide-core
	cp vfide-mac.sh verifast-$(VFVERSION)/bin/vfide
	cp -R ~/Desktop/GtkDemo.app/Contents/Resources/* verifast-$(VFVERSION)
endif
	cp -R ../examples verifast-$(VFVERSION)
	cp -R ../help verifast-$(VFVERSION)
	cp -R ../tests verifast-$(VFVERSION)
	cp -R ../tutorial_solutions verifast-$(VFVERSION)
	mkdir verifast-$(VFVERSION)/tutorial
	cd verifast-$(VFVERSION)/tutorial_solutions; for f in *.c; do ../bin/vfstrip < $$f > ../tutorial/$$f; done; cd ../..
	cp ../testsuite.mysh verifast-$(VFVERSION)
	cp ../test.sh verifast-$(VFVERSION)
