test: verifastz3.opt vfidez3.opt
	./verifastz3.opt ../examples/linkedlist.c
	./verifastz3.opt ../examples/linkedlist2.c
	./verifastz3.opt ../examples/Composite.c
	./verifastz3.opt ../examples/composite4.c
	./verifastz3.opt ../examples/sorted_bintree.c
	./verifastz3.opt -c ../examples/iter.c
	./verifastz3.opt -c ../examples/java/Tree.java
	./verifastz3.opt -c ../examples/java/Tree2/Tree.java
	./verifastz3.opt -c ../examples/java/Tree3/Tree.java
	cd ../examples/chat; ../../src/verifastz3.opt stringBuffers.c sockets.o threading.o lists.o -allow_assume chat.c
	./verifastz3.opt -c ../examples/chatbot/bot.c

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

verifast: vfversion_cmo proverapi.cmo simplex.cmo redux.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o verifast -I $(Z3)/ocaml unix.cma $(Z3)/ocaml/z3.cma proverapi.cmo nums.cma simplex.cmo redux.cmo z3prover.cmo vfversion.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifastZ3: vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o verifastZ3 -I $(Z3)/ocaml unix.cma nums.cma $(Z3)/ocaml/z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml $(Z3)/ocaml/z3_stubs.obj $(Z3)/bin/z3.lib $(OCAMLLIB)/libcamlidl.lib ole32.lib

vfideZ3: vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfide.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o vfideZ3 -I $(Z3)/ocaml -I +lablgtk2 lablgtk.cma gtkInit.cmo unix.cma nums.cma $(Z3)/ocaml/z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfide.ml $(Z3)/ocaml/z3_stubs.obj $(Z3)/bin/z3.lib $(OCAMLLIB)/libcamlidl.lib ole32.lib -ccopt "/link /LIBPATH:"$(GTKLIB)

vfidez3.opt: vfversion_cmx proverapi.cmx z3prover.cmx verifast.cmx verifastPluginZ3.ml vfide.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o vfidez3.opt -I $(Z3)/ocaml -I +lablgtk2 lablgtk.cmxa gtkInit.cmx $(OCAMLLIB)/libcamlidl.a unix.cmxa nums.cmxa z3.cmxa proverapi.cmx z3prover.cmx vfversion.cmx verifast.cmx verifastPluginZ3.ml vfide.ml -ccopt "-L$(Z3)/lib" -cclib -lz3 -cclib -lz3stubs

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

verifastz3.opt: vfversion_cmx proverapi.cmx z3prover.cmx verifast.cmx verifastPluginZ3.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifastz3.opt -I $(Z3)/ocaml unix.cmxa nums.cmxa z3.cmxa proverapi.cmx z3prover.cmx vfversion.cmx verifast.cmx verifastPluginZ3.ml vfconsole.ml -ccopt "-I$(Z3)/ocaml -L$(Z3)/bin -L$(Z3)/lib" -cclib -lz3 -cclib -lz3stubs $(OCAMLLIB)/libcamlidl.a

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
	cp ../Z3.LICENSE.txt verifast-$(VFVERSION)
	cp assume.vfmanifest crt.vfmanifest prelude.h verifast-$(VFVERSION)/bin
	cp verifastz3.opt verifast-$(VFVERSION)/bin/verifast-core
	cp vfidez3.opt verifast-$(VFVERSION)/bin/vfide-core
	cp verifast.sh verifast-$(VFVERSION)/bin/verifast
	cp vfide.sh verifast-$(VFVERSION)/bin/vfide
	cp $(Z3)/lib/libz3.so verifast-$(VFVERSION)/bin
	mkdir verifast-$(VFVERSION)/examples
	cp ../examples/Composite.c verifast-$(VFVERSION)/examples
	cd verifast-$(VFVERSION)/examples; cp ../../../examples/composite4.c .
	cd verifast-$(VFVERSION)/examples; cp ../../../examples/counter.c .
	cd verifast-$(VFVERSION)/examples; cp ../../../examples/counter_with_pred.c .
	cd verifast-$(VFVERSION)/examples; cp ../../../examples/iter.c .
	cd verifast-$(VFVERSION)/examples; cp ../../../examples/linkedlist.c .
	cd verifast-$(VFVERSION)/examples; cp ../../../examples/linkedlist2.c .
	cd verifast-$(VFVERSION)/examples; cp ../../../examples/malloc.h .
	cd verifast-$(VFVERSION)/examples; cp ../../../examples/sorted_bintree.c .
	cd verifast-$(VFVERSION)/examples; cp ../../../examples/stdlib.h .
	cd verifast-$(VFVERSION)/examples; cp ../../../examples/verify.sh .
	cd verifast-$(VFVERSION)/examples; mkdir chat
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/bool.h .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/chat.c .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/helloworld_locking.c .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/helloworld_threading.c .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/lists.c .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/lists.h .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/lists.vfmanifest .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/malloc.h .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/socketlib.c .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/socketlib.h .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/sockets.c .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/sockets.h .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/sockets.vfmanifest .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/stdlib.h .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/string.h .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/stringBuffers.c .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/stringBuffers.h .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/stringBuffersExt.h .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/threading.c .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/threading.h .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/threading.vfmanifest .
	cd verifast-$(VFVERSION)/examples/chat; cp ../../../../examples/chat/verify.sh .
	cd verifast-$(VFVERSION)/examples; mkdir chatbot
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/bool.h .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/bot.c .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/lists.c .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/lists.h .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/malloc.h .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/socketlib.c .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/socketlib.h .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/sockets.c .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/sockets.h .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/stringBuffers.c .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/stringBuffers.h .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/stringBuffersExt.h .
	cd verifast-$(VFVERSION)/examples/chatbot; cp ../../../../examples/chatbot/verify.sh .
	cd verifast-$(VFVERSION)/examples; mkdir java
	cd verifast-$(VFVERSION)/examples/java; cp ../../../../examples/java/Tree.java .
	cd verifast-$(VFVERSION)/examples/java; cp ../../../../examples/java/Tree2/Tree.java Tree2.java
	cd verifast-$(VFVERSION)/examples/java; cp ../../../../examples/java/Tree3/Tree.java Tree3.java
	cd verifast-$(VFVERSION)/examples/java; cp ../../../../examples/java/verify.sh .

