# Note: Do not use executable names with dots in them. (See <http://caml.inria.fr/mantis/view.php?id=4719>.)

OPT_OPTIONS=-g

test: verifast.exe vfide.exe mysh.exe
	time < nl.txt
	cd ..
	mysh < src\testsuite.mysh
	cd src
	time < nl.txt

mysh.exe: mysh.ml
	ocamlopt.opt -o mysh.exe mysh.ml

clean:
	del *.cm* *.obj *.exe

refman:
	cd ..\doc\refman
	pdflatex refman.tex
	pdflatex refman.tex
	pdflatex refman.tex
	cd ..\..\src

reduxtest: verifastredux_opt.exe
	cd ..\examples
	..\src\verifastredux_opt -c args.c
#	..\src\verifastredux_opt composite.c
	..\src\verifastredux_opt -c contrib.c
	..\src\verifastredux_opt -disable_overflow_check counter.c
	..\src\verifastredux_opt -disable_overflow_check counter_with_pred.c
	..\src\verifastredux_opt -shared doubly_linked_list.c
	..\src\verifastredux_opt -disable_overflow_check expr.c
	..\src\verifastredux_opt -c -disable_overflow_check fractions-counting.c
	..\src\verifastredux_opt ghost_field.c
	..\src\verifastredux_opt -shared goto.c
	..\src\verifastredux_opt -c ifs.c
#	..\src\verifastredux_opt map.c
	..\src\verifastredux_opt -shared odd_even_lemmas.c
#	..\src\verifastredux_opt polytest.c
	..\src\verifastredux_opt -disable_overflow_check -shared stack.c
	..\src\verifastredux_opt swap.c
	..\src\verifastredux_opt linkedlist.c
	..\src\verifastredux_opt linkedlist2.c
	..\src\verifastredux_opt composite4.c
#	..\src\verifastredux_opt sorted_bintree.c
	..\src\verifastredux_opt -c iter.c
	cd java
#	..\..\src\verifastredux_opt -c Tree.java
#	..\..\src\verifastredux_opt -c Tree2.java
	cd ..
	cd chat
	..\..\src\verifastredux_opt -c stringBuffers.c
#	..\..\src\verifastredux_opt stringBuffers.c sockets.o threading.o lists.o -allow_assume chat.c
	cd ..
	cd chatbot
	..\..\src\verifastredux_opt -c bot.c
	cd ..

Printexc_proxy.cmx:
	copy Printexc_proxy_311.ml Printexc_proxy.ml
	ocamlopt.opt -c Printexc_proxy.ml

record_backtrace.cmo: record_backtrace.ml
	ocamlc.opt -c record_backtrace.ml

record_backtrace.cmx: record_backtrace.ml
	ocamlopt.opt -c record_backtrace.ml

vfversion.cmi: vfversion.mli
	ocamlc -c vfversion.mli

vfversion_cmo: vfversion.cmi
	ocaml generate_vfversion.ml
	ocamlc -c vfversion.ml

vfversion_cmx: vfversion.cmi
	ocaml generate_vfversion.ml
	ocamlopt.opt $(OPT_OPTIONS) -c vfversion.ml

verifastRedux.exe: vfversion_cmo proverapi.cmo simplex.cmo redux.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml
	ocamlc -warn-error F -w p -g -pp camlp4o -o verifastRedux.exe unix.cma proverapi.cmo nums.cma simplex.cmo redux.cmo vfversion.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml

verifastZ3Redux.exe: vfversion_cmo proverapi.cmo simplex.cmo redux.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o verifast.exe -I $(Z3)\ocaml unix.cma $(Z3)\ocaml\z3.cma proverapi.cmo nums.cma simplex.cmo redux.cmo z3prover.cmo vfversion.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifastZ3.exe: record_backtrace.cmo vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml
	ocamlc -custom -warn-error F -w p -g -pp camlp4o -o verifastZ3.exe -I $(Z3)\ocaml record_backtrace.cmo unix.cma nums.cma $(Z3)\ocaml\z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml $(Z3)\ocaml\z3_stubs.obj $(Z3)\bin\z3.lib $(OCAMLLIB)\libcamlidl.lib ole32.lib

vfideZ3.exe: record_backtrace.cmo vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfide.ml
	time < nl.txt
	ocamlc -custom -warn-error F -g -pp camlp4o -o vfideZ3.exe -I $(Z3)\ocaml -I +lablgtk2 record_backtrace.cmo lablgtk.cma gtkInit.cmo unix.cma nums.cma $(Z3)\ocaml\z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfide.ml $(Z3)\ocaml\z3_stubs.obj $(Z3)\bin\z3.lib $(OCAMLLIB)\libcamlidl.lib ole32.lib -cclib "-L "$(GTKLIB)
	time < nl.txt

vfide.cmx: vfversion.cmi verifast.cmx vfide.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -c -I +lablgtk2 vfide.ml
	time < nl.txt

vfide.exe: Printexc_proxy.cmx record_backtrace.cmx vfversion_cmx proverapi.cmx z3prover.cmx verifast.cmx verifastPluginZ3.ml vfide.cmx
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -pp camlp4o -o vfide.exe -I $(Z3)\ocaml -I +lablgtk2 record_backtrace.cmx lablgtk.cmxa gtkInit.cmx unix.cmxa nums.cmxa z3.cmxa Printexc_proxy.cmx proverapi.cmx z3prover.cmx vfversion.cmx verifast.cmx verifastPluginZ3.ml vfide.cmx -cclib "-L "$(GTKLIB)
	time < nl.txt

vfideredux_opt.exe: Printexc_proxy.cmx record_backtrace.cmx vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.cmx verifastPluginRedux.ml vfide.cmx
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -pp camlp4o -o vfideredux_opt.exe -I +lablgtk2 record_backtrace.cmx lablgtk.cmxa gtkInit.cmx unix.cmxa Printexc_proxy.cmx proverapi.cmx nums.cmxa simplex.cmx redux.cmx vfversion.cmx verifast.cmx verifastPluginRedux.ml vfide.cmx -cclib "-L "$(GTKLIB)

verifast.cmx: vfversion.cmi proverapi.cmx verifast.ml 
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -pp camlp4o -c proverapi.cmx verifast.ml
	time < nl.txt

verifast.cmo: vfversion.cmi proverapi.cmo verifast.ml
	time < nl.txt
	ocamlc.opt -warn-error F -w p -g -pp camlp4o -c verifast.ml
	time < nl.txt

simplex.cmo: simplex.ml
	ocamlc -warn-error F -g -c simplex.ml

proverapi.cmo: proverapi.ml
	ocamlc -warn-error F -g -c proverapi.ml

redux.cmo: proverapi.cmo simplex.cmo redux.ml
	ocamlc -warn-error F -w p -g -c redux.ml

z3prover.cmo: proverapi.cmo z3prover.ml
	ocamlc -warn-error F -g -c -I $(Z3)\ocaml z3prover.ml

verifastz3redux_opt.exe: record_backtrace.cmx vfversion_cmx proverapi.cmx redux.cmx z3prover.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -pp camlp4o -o verifastz3redux_opt.exe -I $(Z3)\ocaml record_backtrace.cmx ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa z3.cmxa proverapi.cmx redux.cmx z3prover.cmx vfversion.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifast.exe: record_backtrace.cmx vfversion_cmx proverapi.cmx z3prover.cmx verifast.cmx verifastPluginZ3.ml vfconsole.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -pp camlp4o -o verifast.exe -I $(Z3)\ocaml record_backtrace.cmx unix.cmxa nums.cmxa z3.cmxa proverapi.cmx z3prover.cmx vfversion.cmx verifast.cmx verifastPluginZ3.ml vfconsole.ml
	time < nl.txt

proverapi.cmx: proverapi.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -c proverapi.ml

simplex.cmx: simplex.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -c simplex.cmx simplex.ml

redux.cmx: proverapi.cmx simplex.cmx redux.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -c redux.ml

z3prover.cmx: proverapi.cmx z3prover.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -c -I $(Z3)\ocaml z3.cmxa proverapi.cmx z3prover.ml

verifastredux_opt.exe: record_backtrace.cmx vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.cmx verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -pp camlp4o -o verifastRedux_opt.exe record_backtrace.cmx unix.cmxa nums.cmxa proverapi.cmx simplex.cmx redux.cmx vfversion.cmx verifast.cmx verifastPluginRedux.ml vfconsole.ml

release: test refman
	mkdir verifast-$(VFVERSION)
	cd verifast-$(VFVERSION)
	copy $(Z3)\LICENSE.txt z3.LICENSE.txt
	mkdir bin
	cd bin
	copy ..\..\assume.vfmanifest
	copy ..\..\crt.vfmanifest
	xcopy $(GTKLIB)\..\bin\*.dll .
	copy ..\..\prelude.h
	copy ..\..\stdlib.h
	copy ..\..\malloc.h
	copy ..\..\string.h
	copy ..\..\verifast.exe verifast.exe
	copy ..\..\vfide.exe vfide.exe
	copy ..\..\mysh.exe mysh.exe
	xcopy /E /I ..\..\rt rt
	copy $(Z3)\bin\z3.dll
	xcopy /E $(Z3)\bin\Microsoft.VC90.CRT .
	cd ..
	mkdir doc
	cd doc
	copy ..\..\..\doc\refman\refman.pdf
	cd ..
	xcopy /E /I ..\..\examples examples
	xcopy /E /I ..\..\tests tests
	copy ..\..\src\testsuite.mysh
	copy ..\..\test.bat
