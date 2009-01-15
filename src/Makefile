test: verifastz3.opt.exe vfidez3.opt.exe
	cd ..\examples
	..\src\verifastz3.opt linkedlist.c
	..\src\verifastz3.opt linkedlist2.c
	..\src\verifastz3.opt composite.c
	..\src\verifastz3.opt composite4.c
	..\src\verifastz3.opt sorted_bintree.c
	..\src\verifastz3.opt -c iter.c
	cd java
	..\..\src\verifastz3.opt -disable_overflow_check -c Counter.java
	..\..\src\verifastz3.opt -c Tree.java
	..\..\src\verifastz3.opt -c Tree2.java
	..\..\src\verifastz3.opt -c Tree3.java
	..\..\src\verifastz3.opt -c Iterator.java
	cd ..
	cd chat
	..\..\src\verifastz3.opt stringBuffers.c sockets.o threading.o lists.o -allow_assume chat.c
	cd ..
	cd chatbot
	..\..\src\verifastz3.opt -c bot.c
	cd ..
	cd ..\src

reduxtest: verifastredux.opt.exe
	cd ..\examples
	..\src\verifastredux.opt linkedlist.c
	..\src\verifastz3.opt linkedlist2.c
#	..\src\verifastredux.opt composite.c
	..\src\verifastredux.opt composite4.c
#	..\src\verifastredux.opt sorted_bintree.c
	..\src\verifastredux.opt -c iter.c
	cd java
#	..\..\src\verifastredux.opt -c Tree.java
#	..\..\src\verifastredux.opt -c Tree2.java
	cd ..
	cd chat
	..\..\src\verifastredux.opt -c stringBuffers.c
#	..\..\src\verifastredux.opt stringBuffers.c sockets.o threading.o lists.o -allow_assume chat.c
	cd ..
	cd chatbot
	..\..\src\verifastz3.opt -c bot.c
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

verifast.exe: vfversion_cmo proverapi.cmo simplex.cmo redux.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o verifast.exe -I $(Z3)\ocaml unix.cma $(Z3)\ocaml\z3.cma proverapi.cmo nums.cma simplex.cmo redux.cmo z3prover.cmo vfversion.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifastZ3.exe: vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o verifastZ3.exe -I $(Z3)\ocaml unix.cma nums.cma $(Z3)\ocaml\z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml $(Z3)\ocaml\z3_stubs.obj $(Z3)\bin\z3.lib $(OCAMLLIB)\libcamlidl.lib ole32.lib

vfideZ3.exe: vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfide.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o vfideZ3.exe -I $(Z3)\ocaml -I +lablgtk2 lablgtk.cma gtkInit.cmo unix.cma nums.cma $(Z3)\ocaml\z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfide.ml $(Z3)\ocaml\z3_stubs.obj $(Z3)\bin\z3.lib $(OCAMLLIB)\libcamlidl.lib ole32.lib -ccopt "/link /LIBPATH:"$(GTKLIB)

vfideZ3.opt.exe: vfversion_cmx proverapi.cmx z3prover.cmx verifast.cmx verifastPluginZ3.ml vfide.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o vfidez3.opt.exe -I $(Z3)\ocaml -I +lablgtk2 lablgtk.cmxa gtkInit.cmx ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa nums.cmxa z3.cmxa proverapi.cmx z3prover.cmx vfversion.cmx verifast.cmx verifastPluginZ3.ml vfide.ml -ccopt "/link /LIBPATH:"$(GTKLIB)

vfideredux.opt.exe: vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.cmx verifastPluginRedux.ml vfide.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o vfideredux.opt.exe -I +lablgtk2 lablgtk.cmxa gtkInit.cmx unix.cmxa proverapi.cmx nums.cmxa simplex.cmx redux.cmx vfversion.cmx verifast.cmx verifastPluginRedux.ml vfide.ml -ccopt "/link /LIBPATH:$(GTKLIB)"

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
	ocamlc -warn-error F -g -c -I $(Z3)\ocaml z3prover.ml

verifast.opt.exe: vfversion_cmx proverapi.cmx redux.cmx z3prover.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifast.opt.exe -I $(Z3)\ocaml ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa z3.cmxa proverapi.cmx redux.cmx z3prover.cmx vfversion.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifastz3.opt.exe: vfversion_cmx proverapi.cmx z3prover.cmx verifast.ml verifastPluginZ3.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifastz3.opt.exe -I $(Z3)\ocaml ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa nums.cmxa z3.cmxa proverapi.cmx z3prover.cmx vfversion.cmx verifast.ml verifastPluginZ3.ml vfconsole.ml

proverapi.cmx: proverapi.ml
	ocamlopt.opt -warn-error F -c proverapi.ml

simplex.cmx: simplex.ml
	ocamlopt.opt -warn-error F -c simplex.cmx simplex.ml

redux.cmx: proverapi.cmx simplex.cmx redux.ml
	ocamlopt.opt -warn-error F -c redux.ml

z3prover.cmx: proverapi.cmx z3prover.ml
	ocamlopt.opt -warn-error F -c -I $(Z3)\ocaml z3.cmxa proverapi.cmx z3prover.ml

verifastRedux.opt.exe: vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt -warn-error F -pp camlp4o -o verifastRedux.opt.exe unix.cmxa nums.cmxa proverapi.cmx simplex.cmx redux.cmx vfversion.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml

release: test
	mkdir verifast-$(VFVERSION)
	cd verifast-$(VFVERSION)
	copy $(Z3)\LICENSE.txt z3.LICENSE.txt
	mkdir bin
	cd bin
	copy ..\..\assume.vfmanifest
	copy ..\..\crt.vfmanifest
	xcopy $(GTKLIB)\..\bin\*.dll .
	copy ..\..\prelude.h
	copy ..\..\verifastz3.opt.exe verifast.exe
	copy ..\..\vfidez3.opt.exe vfide.exe
	copy $(Z3)\bin\z3.dll
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
	copy ..\..\..\examples\malloc.h
	copy ..\..\..\examples\sorted_bintree.c
	copy ..\..\..\examples\stdlib.h
	copy ..\..\..\examples\verify.bat
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
	copy ..\..\..\..\examples\chat\malloc.h
	copy ..\..\..\..\examples\chat\socketlib.c
	copy ..\..\..\..\examples\chat\socketlib.h
	copy ..\..\..\..\examples\chat\sockets.c
	copy ..\..\..\..\examples\chat\sockets.h
	copy ..\..\..\..\examples\chat\sockets.vfmanifest
	copy ..\..\..\..\examples\chat\stdlib.h
	copy ..\..\..\..\examples\chat\string.h
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
	copy ..\..\..\..\examples\chatbot\malloc.h
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
	copy ..\..\..\..\examples\java\Tree2.java
	copy ..\..\..\..\examples\java\verify.bat
	cd ..
	cd ..
