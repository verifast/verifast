include ../GNUmakefile.settings

# OS detection
ifeq ($(OS), Linux)
  LINUX        = yes
  OS_SUPPORTED = yes
endif
ifeq ($(OS), Darwin)
  MAC          = yes
  OS_SUPPORTED = yes
endif
# TODO: Add support for Cygwin

# GSourceView2 for MAC
ifdef MAC
  GTKSOURCEVIEW      = -I macos GSourceView2.cmx
  GTKSOURCEVIEW_DEPS = macos/GSourceView2.cmx
  GTKSOURCEVIEW_LIBS =
else
  ifdef LABLGTK2
    GTKSOURCEVIEW      = -I ${LABLGTK2} lablgtksourceview2.cmxa
    GTKSOURCEVIEW_DEPS =
  else
    GTKSOURCEVIEW      = lablgtksourceview2.cmxa
    GTKSOURCEVIEW_DEPS =
  endif
  ifdef LABLLIBS
    GTKSOURCEVIEW_LIBS = ${LABLLIBS}
  else
    GTKSOURCEVIEW_LIBS =
  endif
endif


# Z3 configuration
ifdef Z3
  Z3DEPS  = z3prover.cmx verifastPluginZ3.ml
  Z3ARGS  = -I $(Z3)/ocaml z3.cmxa z3prover.cmx verifastPluginZ3.ml \
            -ccopt "-I$(Z3)/ocaml -L$(Z3)/bin -L$(Z3)/lib" \
            -cclib -lz3-gmp -cclib -lz3stubs $(OCAMLLIB)/libcamlidl.a
  LDLPATH = $(Z3)/lib
else ifdef Z3V2
  Z3      = $(Z3V2)
  Z3DEPS  = z3v2prover.cmx verifastPluginZ3v2.ml
  Z3ARGS  = -I $(Z3)/ocaml z3.cmxa z3v2prover.cmx verifastPluginZ3v2.ml \
            -ccopt "-I$(Z3)/ocaml -L$(Z3)/bin -L$(Z3)/lib" \
            -cclib -lz3-gmp -cclib -lz3stubs $(OCAMLLIB)/libcamlidl.a
  LDLPATH = $(Z3)/lib
else ifdef NOZ3
  Z3DEPS  =
  Z3ARGS  =
  LDLPATH =
else
  $(error Neither Z3, Z3V2, nor NOZ3 is defined. Please check your \
   ../GNUmakefile.settings)
endif

# Number of CPUs
# TODO: Isn't there /sys on Darwin, Linux and Cygwin?
ifdef MAC
  NUMCPU := $(shell sysctl -n hw.ncpu)
else
  NUMCPU := $(shell cat /proc/cpuinfo | grep 'processor' | wc -l)
endif


# Shorthands to set up environments
SET_LDD = export CAML_LD_LIBRARY_PATH=$$CAML_LD_LIBRARY_PATH:GTKSOURCEVIEW_LIBS
SET_ENV = export PATH=$(CWD)/../bin/:$$PATH; \
          export LD_LIBRARY_PATH=$(LDLPATH):$$LD_LIBRARY_PATH


all: build test

build: env \
       ../bin/mysh ../bin/verifast ../bin/vfide ../bin/main_class ../bin/java_card_applet ../bin/dlsymtool \
       ../bin/vfstrip ../bin/list.vfmanifest \
       ../bin/raw_ghost_lists.vfmanifest ../bin/listex.vfmanifest \
       ../bin/arrays.vfmanifest

test_plugin: build
	$(SET_ENV); \
	cd ../examples/plugin; make clean && make

test: build test_plugin
	$(SET_ENV); \
        cd ..; bin/mysh -cpus $(NUMCPU) < testsuite.mysh

env:
	@echo "Configuration:"
	@echo "---------------------"
ifdef OS_SUPPORTED
	@echo "OS                 $(OS)"
else
	$(error Unknown operating system: $(OS))
endif
	@echo "NUMCPU             $(NUMCPU)"
	@echo "OCAMLBIN           $(OCAMLBIN)"
	@echo "OCAMLLIB           $(OCAMLLIB)"
	@echo "CWD                $(CWD)"
	@echo "Z3                 $(Z3)"
	@echo "Z3V2               $(Z3V2)"
	@echo "Z3DEPS             $(Z3DEPS)"
	@echo "LDLPATH            $(LDLPATH)"
	@echo "GTKSOURCEVIEW      $(GTKSOURCEVIEW)"
	@echo "GTKSOURCEVIEW_LIBS ${GTKSOURCEVIEW_LIBS}"

clean:
	rm -f *.cm*
	rm -f *.o *.a
	cd ../bin; rm -f verifast vfide dlsymtool vfstrip mysh \
         arrays.vfmanifest list.vfmanifest listex.vfmanifest \
         raw_ghost_lists.vfmanifest
	rm -f macos/*.cm* macos/*.o
	rm -f a.out
	${MAKE} -C linux -f GNUmakefile clean

distclean: clean

../bin/list.vfmanifest: ../bin/list.c ../bin/list.gh
	$(SET_ENV); cd ../bin; ./verifast -c -emit_vfmanifest list.c

../bin/listex.vfmanifest: ../bin/listex.c ../bin/listex.gh \
 ../bin/list.vfmanifest
	$(SET_ENV); cd ../bin; ./verifast -c -emit_vfmanifest listex.c

../bin/arrays.vfmanifest: ../bin/arrays.c ../bin/arrays.gh \
 ../bin/list.vfmanifest
	$(SET_ENV); cd ../bin; ./verifast -c -emit_vfmanifest arrays.c

../bin/raw_ghost_lists.vfmanifest: ../bin/raw_ghost_lists.c \
 ../bin/raw_ghost_lists.gh ../bin/list.vfmanifest
	$(SET_ENV); cd ../bin; ./verifast -c -emit_vfmanifest raw_ghost_lists.c

../bin/vfstrip: vfstrip.ml
	${OCAMLOPTOPT} -o ../bin/vfstrip vfstrip.ml

../bin/main_class: main_class.ml
	${OCAMLOPTOPT} -o ../bin/main_class main_class.ml

../bin/java_card_applet: java_card_applet.ml
	${OCAMLOPTOPT} -o ../bin/java_card_applet java_card_applet.ml

../bin/dlsymtool: dlsymtool.ml
	${OCAMLOPTOPT} -o ../bin/dlsymtool dlsymtool.ml

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
	${OCAMLOPT} -c Printexc_proxy.ml

ifdef MAC
Fonts.cmx: Fonts_mac.ml
	cp Fonts_mac.ml Fonts.ml
	${OCAMLOPT} -c Fonts.ml
else
Fonts.cmx: Fonts_default.ml
	cp Fonts_default.ml Fonts.ml
	${OCAMLOPT} -c Fonts.ml
endif

../bin/mysh: Fonts.cmx mysh.ml
	${OCAMLOPTOPT} -thread -o ../bin/mysh unix.cmxa threads.cmxa Fonts.cmx mysh.ml

vfversion.cmi: vfversion.mli
	${OCAMLC} -c vfversion.mli

vfversion_cmo: vfversion.cmi
	${OCAML} generate_vfversion.ml
	${OCAMLC} -c vfversion.ml

vfversion_cmx: vfversion.cmi
	${OCAML} generate_vfversion.ml
	${OCAMLOPT} -c vfversion.ml

verifastRedux: vfversion_cmo proverapi.cmo simplex.cmo redux.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml
	${OCAMLC} -warn-error F -w p -g -pp ${CAMLP4O} -o verifastRedux unix.cma proverapi.cmo nums.cma simplex.cmo redux.cmo vfversion.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml

verifastZ3: vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml
ifdef Z3V2
	$(error "Z3V2 is defined.")
endif
	${OCAMLC} -custom -warn-error F -g -pp ${CAMLP4O} -o verifastZ3 -I $(Z3)/ocaml unix.cma nums.cma $(Z3)/ocaml/z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml $(Z3)/ocaml/z3_stubs.obj $(Z3)/bin/z3.lib $(OCAMLLIB)/libcamlidl.lib ole32.lib

verifastZ3v2: vfversion_cmo proverapi.cmo z3v2prover.cmo verifast.cmo verifastPluginZ3v2.ml vfconsole.ml
ifndef Z3V2
	$(error "Z3V2 is not defined.")
endif
	${OCAMLC} -custom -warn-error F -g -pp ${CAMLP4O} -o verifastZ3v2 -I ./linux -I $(Z3)/ocaml unix.cma nums.cma $(Z3)/ocaml/z3.ml proverapi.cmo z3v2prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3v2.ml vfconsole.ml $(Z3)/ocaml/z3_stubs.obj $(Z3)/bin/z3.lib $(OCAMLLIB)/libcamlidl.lib ole32.lib

vfideZ3: vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfide.ml
	$(SET_LDD); ${OCAMLC} -custom -warn-error F -g -pp ${CAMLP4O} -o vfideZ3 -I $(Z3)/ocaml -I +lablgtk2 lablgtk.cma gtkInit.cmo unix.cma nums.cma $(Z3)/ocaml/z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfide.ml $(Z3)/ocaml/z3_stubs.obj $(Z3)/bin/z3.lib $(OCAMLLIB)/libcamlidl.lib ole32.lib -ccopt "/link /LIBPATH:"$(GTKLIB)

mynum.cmx: mynum.ml
	${OCAMLOPTOPT} -c nums.cmxa mynum.ml

ifdef MAC
macos/GSourceView2.cmx: macos/GSourceView2.ml
	cd macos; ${OCAMLOPTOPT} -c -I +lablgtk2 GSourceView2.ml
endif

../bin/vfide: Printexc_proxy.cmx vfversion_cmx proverapi.cmx util.cmx stats.cmx lexer.cmx ast.cmx parser.cmx verifast0.cmx verifast1.cmx assertions.cmx verify_expr.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3DEPS) Fonts.cmx $(GTKSOURCEVIEW_DEPS) vfide.ml
	$(SET_LDD); ${OCAMLOPTOPT} -warn-error F -pp ${CAMLP4O} -o ../bin/vfide -I +lablgtk2 lablgtk.cmxa $(GTKSOURCEVIEW) gtkInit.cmx unix.cmxa nums.cmxa -I ./linux Perf.cmxa proverapi.cmx Printexc_proxy.cmx vfversion.cmx dynlink.cmxa DynType.cmx plugins.cmx plugins_private.cmx plugins2.cmx util.cmx stats.cmx lexer.cmx ast.cmx parser.cmx verifast0.cmx verifast1.cmx assertions.cmx verify_expr.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3ARGS) Fonts.cmx vfide.ml

vfideredux.opt: vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.cmx verifastPluginRedux.ml vfide.ml
	$(SET_LDD); ${OCAMLOPTOPT} -warn-error F -pp ${CAMLP4O} -o vfideredux.opt -I +lablgtk2 lablgtk.cmxa gtkInit.cmx unix.cmxa proverapi.cmx nums.cmxa simplex.cmx redux.cmx vfversion.cmx verifast.cmx verifastPluginRedux.ml vfide.ml

linux/Perf.cmxa: linux/Perf.ml linux/Stopwatch.mli linux/caml_stopwatch.c
	${MAKE} -C linux OCAMLOPTOPT=${OCAMLOPTOPT}

DynType.mli: ../examples/plugin/DynType.mli
	cat generated_file_warning.txt ../examples/plugin/DynType.mli > DynType.mli

DynType.cmi: DynType.mli
	${OCAMLOPTOPT} -c DynType.mli

DynType.cmx: DynType.cmi DynType.ml
	${OCAMLOPTOPT} -c DynType.ml

plugins.mli: ../examples/plugin/plugins.mli
	cat generated_file_warning.txt ../examples/plugin/plugins.mli > plugins.mli

plugins.cmi: DynType.cmi plugins.mli
	${OCAMLOPTOPT} -c plugins.mli

plugins.cmx: DynType.cmx plugins.cmi plugins.ml
	${OCAMLOPTOPT} -c plugins.ml

plugins_private.cmx: plugins.cmx plugins_private.ml
	${OCAMLOPTOPT} -c plugins_private.ml

plugins2.mli: ../examples/plugin/plugins2.mli
	cat generated_file_warning.txt ../examples/plugin/plugins2.mli > plugins2.mli

plugins2.cmi: plugins.cmi plugins2.mli
	${OCAMLOPTOPT} -c plugins2.mli

plugins2.cmx: plugins_private.cmx plugins2.cmi plugins2.ml
	${OCAMLOPTOPT} -c plugins2.ml

pa_verifast.cmo: pa_verifast.ml
	${OCAMLC} -I +camlp4 dynlink.cma camlp4lib.cma -pp "${CAMLP4O} pa_extend.cmo q_MLast.cmo" pa_verifast.ml

util.cmx: linux/Perf.cmxa vfversion.cmi proverapi.cmx plugins2.cmx pa_verifast.cmo util.ml
	${OCAMLOPTOPT} -w p -warn-error FSU -c -I ./linux util.ml

stats.cmx: util.cmx stats.ml
	${OCAMLOPTOPT} -w p -warn-error FSU -c -I ./linux stats.ml

lexer.cmx: stats.cmx lexer.ml
	${OCAMLOPTOPT} -w p -warn-error FSU -c -I ./linux lexer.ml

ast.cmx: lexer.cmx ast.ml
	${OCAMLOPTOPT} -w p -warn-error FSU -c -I ./linux ast.ml

parser.cmx: ast.cmx parser.ml
	${OCAMLOPTOPT} -w p -warn-error FSU -pp ${CAMLP4O} -c -I ./linux parser.ml

verifast0.cmx: parser.cmx verifast0.ml
	${OCAMLOPTOPT} -w p -warn-error FSU -c -I ./linux verifast0.ml

verifast1.cmx: verifast0.cmx verifast1.ml
	${OCAMLOPTOPT} -w p -warn-error FSU -c -I ./linux verifast1.ml

assertions.cmx: verifast1.cmx assertions.ml
	${OCAMLOPTOPT} -w p -warn-error FSU -c -I ./linux assertions.ml

verify_expr.cmx: assertions.cmx verify_expr.ml
	${OCAMLOPTOPT} -w p -warn-error FSU -c -I ./linux verify_expr.ml

verifast.cmx: verify_expr.cmx verifast.ml
	${OCAMLOPTOPT} -w p -warn-error FSU -c -I ./linux verifast.ml

verifast.cmo: vfversion.cmi proverapi.cmo verifast.ml
	${OCAMLCOPT} -warn-error F -g -pp ${CAMLP4O} -I ./linux -c verifast.ml

simplex.cmo: simplex.ml
	${OCAMLC} -warn-error F -g -c simplex.ml

proverapi.cmo: proverapi.ml
	${OCAMLC} -warn-error F -g -c proverapi.ml

redux.cmo: proverapi.cmo simplex.cmo redux.ml
	${OCAMLC} -warn-error F -w p -g -c redux.ml

z3prover.cmo: proverapi.cmo z3prover.ml linux/Perf.cmxa
ifdef Z3V2
	$(error "Z3V2 is defined.")
endif
	${OCAMLC} -warn-error F -g -c -I $(Z3)/ocaml -I ./linux z3prover.ml

z3v2prover.cmo: proverapi.cmo z3v2prover.ml linux/Perf.cmxa
ifndef Z3V2
	$(error "Z3V2 is not defined.")
endif
	${OCAMLC} -warn-error F -g -c -I $(Z3)/ocaml -I ./linux z3v2prover.ml

verifast.opt: vfversion_cmx proverapi.cmx redux.cmx z3prover.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	${OCAMLOPTOPT} -warn-error F -pp ${CAMLP4O} -o verifast.opt -I $(Z3)/ocaml ole32.lib $(OCAMLLIB)/libcamlidl.lib unix.cmxa z3.cmxa proverapi.cmx redux.cmx z3prover.cmx vfversion.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

SExpressions.cmi: SExpressions.mli
	${OCAMLOPTOPT} -c SExpressions.mli

SExpressions.cmx: SExpressions.cmi SExpressions.ml
	${OCAMLOPTOPT} -c nums.cmxa SExpressions.ml

SExpressionEmitter.cmi: verifast.cmx SExpressionEmitter.mli
	${OCAMLOPTOPT} -c SExpressionEmitter.mli

SExpressionEmitter.cmx: verifast.cmx SExpressionEmitter.cmi SExpressions.cmx SExpressionEmitter.ml
	${OCAMLOPTOPT} -c nums.cmxa SExpressionEmitter.ml

../bin/verifast: vfversion_cmx proverapi.cmx util.cmx stats.cmx lexer.cmx ast.cmx parser.cmx verifast0.cmx verifast1.cmx assertions.cmx verify_expr.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3DEPS) SExpressions.cmx SExpressionEmitter.cmx vfconsole.ml
	${OCAMLOPTOPT} -warn-error F -pp ${CAMLP4O} -o ../bin/verifast unix.cmxa nums.cmxa -I ./linux Perf.cmxa proverapi.cmx vfversion.cmx dynlink.cmxa DynType.cmx plugins.cmx plugins_private.cmx plugins2.cmx util.cmx stats.cmx lexer.cmx ast.cmx parser.cmx verifast0.cmx verifast1.cmx assertions.cmx verify_expr.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml $(Z3ARGS) SExpressions.cmx SExpressionEmitter.cmx vfconsole.ml

proverapi.cmx: proverapi.ml
	${OCAMLOPTOPT} -warn-error F -c proverapi.ml

simplex.cmi: simplex.mli
	${OCAMLOPTOPT} -c simplex.mli

simplex.cmx: linux/Perf.cmx simplex.cmi simplex.ml
	${OCAMLOPTOPT} -warn-error F -c -I ./linux Perf.cmx simplex.ml

redux.cmx: linux/Perf.cmx proverapi.cmx simplex.cmx redux.ml
	${OCAMLOPTOPT} -warn-error F -c -I ./linux Perf.cmx redux.ml

z3prover.cmx: linux/Perf.cmx proverapi.cmx z3prover.ml
	${OCAMLOPTOPT} -warn-error F -c -I $(Z3)/ocaml z3.cmxa -I ./linux Perf.cmx proverapi.cmx z3prover.ml

z3v2prover.cmx: linux/Perf.cmx proverapi.cmx z3v2prover.ml
	${OCAMLOPTOPT} -warn-error F -c -I $(Z3)/ocaml z3.cmxa -I ./linux Perf.cmx proverapi.cmx z3v2prover.ml

verifastRedux.opt: vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml
	${OCAMLOPTOPT} -warn-error F -pp ${CAMLP4O} -o verifastRedux.opt unix.cmxa nums.cmxa proverapi.cmx simplex.cmx redux.cmx vfversion.cmx verifast.ml verifastPluginRedux.ml vfconsole.ml

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
	cp -R ../javacard_tutorial verifast-$(VFVERSION)
	cp -R ../tests verifast-$(VFVERSION)
	cp -R ../tutorial_solutions verifast-$(VFVERSION)
	mkdir verifast-$(VFVERSION)/tutorial
	cd verifast-$(VFVERSION)/tutorial_solutions; for f in *.c; do ../bin/vfstrip < $$f > ../tutorial/$$f; done; cd ../..
	cp ../testsuite.mysh verifast-$(VFVERSION)
	cp ../test.sh verifast-$(VFVERSION)
