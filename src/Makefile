# Note: Do not use executable names with dots in them. (See <http://caml.inria.fr/mantis/view.php?id=4719>.)

test: verifast.exe vfide.exe
	cd ..\examples
	..\src\verifast linkedlist.c
	..\src\verifast linkedlist2.c
	..\src\verifast composite.c
	..\src\verifast composite4.c
	..\src\verifast sorted_bintree.c
	..\src\verifast iter.c
	..\src\verifast -c args.c
	..\src\verifast swap.c
	..\src\verifast -shared polytest.c
	..\src\verifast -disable_overflow_check expr.c
	..\src\verifast -shared queue.c
	..\src\verifast -c ifs.c
	..\src\verifast -shared goto.c
	cd java
	..\..\src\verifast -disable_overflow_check -c Counter.java
	..\..\src\verifast -c Tree.java
	cd Tree2
	..\..\..\src\verifast -c Tree.java
	cd ..
	cd Tree3
	..\..\..\src\verifast -c Tree.java
	cd ..
	..\..\src\verifast -c Iterator.java
	cd Iterator
	..\..\..\src\verifast -c it.jarsrc
	..\..\..\src\verifast -c prog.jarsrc
	cd ..
	cd ..
	cd chat
	..\..\src\verifast stringBuffers.c sockets.o threading.o lists.o -allow_assume chat.c
	cd ..
	cd chatbot
	..\..\src\verifast -c bot.c
	cd ..
	cd incr_box
	..\..\src\verifast -c incr_box.c
	cd ..
	..\src\verifast -c contrib.c
	..\src\verifast reallittest.c
	cd ..\tests\errors
	..\..\src\verifast -c -allow_should_fail basics.c
	..\..\src\verifast -c -allow_should_fail typecheck1.c
	cd ..\..\src

refman:
	cd ..\doc\refman
	pdflatex refman.tex
	pdflatex refman.tex
	pdflatex refman.tex
	cd ..\..\src

reduxtest: verifastredux_opt.exe
	cd ..\examples
	..\src\verifastredux_opt linkedlist.c
	..\src\verifastredux_opt linkedlist2.c
#	..\src\verifastredux_opt composite.c
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

vfversion.cmi: vfversion.mli
	ocamlc -c vfversion.mli

vfversion_cmo: vfversion.cmi
	ocaml generate_vfversion.ml
	ocamlc -c vfversion.ml

vfversion_cmx: vfversion.cmi
	ocaml generate_vfversion.ml
	ocamlopt -c vfversion.ml

verifastRedux.exe: vfversion_cmo proverapi.cmo simplex.cmo redux.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml
	ocamlc -warn-error F -w p -g -pp camlp4o -o verifastRedux.exe unix.cma proverapi.cmo nums.cma simplex.cmo redux.cmo vfversion.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml

verifastZ3Redux.exe: vfversion_cmo proverapi.cmo simplex.cmo redux.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o verifast.exe -I $(Z3)\ocaml unix.cma $(Z3)\ocaml\z3.cma proverapi.cmo nums.cma simplex.cmo redux.cmo z3prover.cmo vfversion.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifastZ3.exe: vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml
	ocamlc -custom -warn-error F -w p -g -pp camlp4o -o verifastZ3.exe -I $(Z3)\ocaml unix.cma nums.cma $(Z3)\ocaml\z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml $(Z3)\ocaml\z3_stubs.obj $(Z3)\bin\z3.lib $(OCAMLLIB)\libcamlidl.lib ole32.lib

vfideZ3.exe: vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfide.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o vfideZ3.exe -I $(Z3)\ocaml -I +lablgtk2 lablgtk.cma gtkInit.cmo unix.cma nums.cma $(Z3)\ocaml\z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfide.ml $(Z3)\ocaml\z3_stubs.obj $(Z3)\bin\z3.lib $(OCAMLLIB)\libcamlidl.lib ole32.lib -ccopt "/link /LIBPATH:"$(GTKLIB)

vfide.exe: vfversion_cmx proverapi.cmx z3prover.cmx verifast.cmx verifastPluginZ3.ml vfide.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o vfide.exe -I $(Z3)\ocaml -I +lablgtk2 lablgtk.cmxa gtkInit.cmx ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa nums.cmxa z3.cmxa proverapi.cmx z3prover.cmx vfversion.cmx verifast.cmx verifastPluginZ3.ml vfide.ml -ccopt "/link /LIBPATH:"$(GTKLIB)

vfideredux_opt.exe: vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.cmx verifastPluginRedux.ml vfide.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o vfideredux_opt.exe -I +lablgtk2 lablgtk.cmxa gtkInit.cmx unix.cmxa proverapi.cmx nums.cmxa simplex.cmx redux.cmx vfversion.cmx verifast.cmx verifastPluginRedux.ml vfide.ml -ccopt "/link /LIBPATH:$(GTKLIB)"

verifast.cmx: vfversion.cmi proverapi.cmx verifast.ml 
	ocamlopt.opt -warn-error F -pp camlp4o -c proverapi.cmx verifast.ml

verifast.cmo: vfversion.cmi proverapi.cmo verifast.ml
	ocamlc.opt -warn-error F -w p -g -pp camlp4o -c verifast.ml

simplex.cmo: simplex.ml
	ocamlc -warn-error F -g -c simplex.ml

proverapi.cmo: proverapi.ml
	ocamlc -warn-error F -g -c proverapi.ml

redux.cmo: proverapi.cmo simplex.cmo redux.ml
	ocamlc -warn-error F -w p -g -c redux.ml

z3prover.cmo: proverapi.cmo z3prover.ml
	ocamlc -warn-error F -g -c -I $(Z3)\ocaml z3prover.ml

verifastz3redux_opt.exe: vfversion_cmx proverapi.cmx redux.cmx z3prover.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifastz3redux_opt.exe -I $(Z3)\ocaml ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa z3.cmxa proverapi.cmx redux.cmx z3prover.cmx vfversion.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifast.exe: vfversion_cmx proverapi.cmx z3prover.cmx verifast.cmx verifastPluginZ3.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifast.exe -I $(Z3)\ocaml ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa nums.cmxa z3.cmxa proverapi.cmx z3prover.cmx vfversion.cmx verifast.cmx verifastPluginZ3.ml vfconsole.ml

proverapi.cmx: proverapi.ml
	ocamlopt.opt -warn-error F -c proverapi.ml

simplex.cmx: simplex.ml
	ocamlopt.opt -warn-error F -c simplex.cmx simplex.ml

redux.cmx: proverapi.cmx simplex.cmx redux.ml
	ocamlopt.opt -warn-error F -c redux.ml

z3prover.cmx: proverapi.cmx z3prover.ml
	ocamlopt.opt -warn-error F -c -I $(Z3)\ocaml z3.cmxa proverapi.cmx z3prover.ml

verifastRedux_opt.exe: vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifastRedux_opt.exe unix.cmxa nums.cmxa proverapi.cmx simplex.cmx redux.cmx vfversion.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml

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
	copy $(Z3)\bin\z3.dll
	xcopy /E $(Z3)\bin\Microsoft.VC90.CRT .
	cd ..
	mkdir doc
	cd doc
	copy ..\..\..\doc\refman\refman.pdf
	cd ..
	mkdir examples
	cd examples
	copy ..\..\..\examples\Composite.c
	copy ..\..\..\examples\composite4.c
	copy ..\..\..\examples\counter.c
	copy ..\..\..\examples\counter_with_pred.c
	copy ..\..\..\examples\iter.c
	copy ..\..\..\examples\linkedlist.c
	copy ..\..\..\examples\linkedlist2.c
	copy ..\..\..\examples\sorted_bintree.c
	copy ..\..\..\examples\contrib.c
	copy ..\..\..\examples\verify.bat
	mkdir incr_box
	cd incr_box
	copy ..\..\..\..\examples\incr_box\incr_box.c
	copy ..\..\..\..\examples\incr_box\threading.h
	cd ..
	mkdir chat
	cd chat
	copy ..\..\..\..\examples\chat\bool.h
	copy ..\..\..\..\examples\chat\chat.c
	copy ..\..\..\..\examples\chat\chat.vcproj
	copy ..\..\..\..\examples\chat\helloworld_locking.c
	copy ..\..\..\..\examples\chat\helloworld_threading.c
	copy ..\..\..\..\examples\chat\lists.c
	copy ..\..\..\..\examples\chat\lists.h
	copy ..\..\..\..\examples\chat\lists.vfmanifest
	copy ..\..\..\..\examples\chat\make.bat
	copy ..\..\..\..\examples\chat\socketlib.c
	copy ..\..\..\..\examples\chat\socketlib.h
	copy ..\..\..\..\examples\chat\sockets.c
	copy ..\..\..\..\examples\chat\sockets.h
	copy ..\..\..\..\examples\chat\sockets.vfmanifest
	copy ..\..\..\..\examples\chat\stringBuffers.c
	copy ..\..\..\..\examples\chat\stringBuffers.h
	copy ..\..\..\..\examples\chat\stringBuffersExt.h
	copy ..\..\..\..\examples\chat\threading.c
	copy ..\..\..\..\examples\chat\threading.h
	copy ..\..\..\..\examples\chat\threading.vfmanifest
	copy ..\..\..\..\examples\chat\verify.bat
	cd ..
	mkdir chatbot
	cd chatbot
	copy ..\..\..\..\examples\chatbot\bool.h
	copy ..\..\..\..\examples\chatbot\bot.c
	copy ..\..\..\..\examples\chatbot\chatbot.vcproj
	copy ..\..\..\..\examples\chatbot\lists.c
	copy ..\..\..\..\examples\chatbot\lists.h
	copy ..\..\..\..\examples\chatbot\socketlib.c
	copy ..\..\..\..\examples\chatbot\socketlib.h
	copy ..\..\..\..\examples\chatbot\sockets.c
	copy ..\..\..\..\examples\chatbot\sockets.h
	copy ..\..\..\..\examples\chatbot\stringBuffers.c
	copy ..\..\..\..\examples\chatbot\stringBuffers.h
	copy ..\..\..\..\examples\chatbot\stringBuffersExt.h
	copy ..\..\..\..\examples\chatbot\verify.bat
	cd ..
	mkdir java
	cd java
	copy ..\..\..\..\examples\java\Tree.java
	copy ..\..\..\..\examples\java\Tree2\Tree.java Tree2.java
	copy ..\..\..\..\examples\java\Tree3\Tree.java Tree3.java
	copy ..\..\..\..\examples\java\Iterator.java
	copy ..\..\..\..\examples\java\Counter.java
	copy ..\..\..\..\examples\java\verify.bat
	mkdir iterator
	cd iterator
	copy ..\..\..\..\..\examples\java\iterator\it.jarsrc
	copy ..\..\..\..\..\examples\java\iterator\Iterator.java
	copy ..\..\..\..\..\examples\java\iterator\IteratorUtil.java
	copy ..\..\..\..\..\examples\java\iterator\Program.java
	copy ..\..\..\..\..\examples\java\iterator\SingletonIterator.java
	cd ..
	cd ..
