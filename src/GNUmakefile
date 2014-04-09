# Builds VeriFast itself. Does *not* build dependencies like lablgtk,ocaml,...

all: build test
.PHONY: all

#------------------------------- Help ---------------------------------------#
help:
	@echo "Builds verifast,vfide,mysh,... but not dependencies."
	@echo "It does not build Z3 bindings, lablgtk bindings, ocaml, ..."
	@echo "Usage: "
	@echo "  make help : print this help"
	@echo "  make env  : print environment variables, i.e. the configuration"
	@echo "  make verifast: only compile verifast (also works without lablgtk)"
	@echo "  make vfide: only compile vfide"
	@echo "  make build: compile everything (do not run tests)"
	@echo "  make      : compile all and run tests"
	@echo "  make clean: remove output and temp files"
	@echo "Tips:"
	@echo "-You can add the option VERBOSE=1 to see more, e.g. 'make build VERBOSE=1'".
	@echo "-You can add -j N to use N cores, e.g. 'make build -j 4'."
.PHONY: help

#------------------------------- Settings -----------------------------------#

include ../GNUmakefile.settings

# Lablgtk configuration
ifndef WITHOUT_LABLGTK
  ifeq ($(OS), Darwin)
    GTKSOURCEVIEW_LFLAGS += -I macos GSourceView2.cmx
    GTKSOURCEVIEW_DEPS   += macos/GSourceView2.cmx
  else
    GTKSOURCEVIEW_LFLAGS += lablgtksourceview2.cmxa
    ifdef LABLGTK2
      GTKSOURCEVIEW_LFLAGS += -I ${LABLGTK2} 
    endif
    GTKSOURCEVIEW_LIBS   += ${LABLLIBS}
  endif
endif

ifeq ($(OS), Cygwin)
  LDLPATHVAR=PATH
else
  LDLPATHVAR=LD_LIBRARY_PATH
endif

# Z3 configuration
ifndef NOZ3
  ifdef Z3
    Z3VERSION = 
  else ifdef Z3V2
    Z3VERSION = v2
    Z3 = $(Z3V2)
  else ifdef Z3V4
    Z3VERSION = v4
    Z3 = $(Z3V4)
  else
    $(error Neither Z3, Z3V2, Z3V4, nor NOZ3 is defined. Please check your \
     ../GNUmakefile.settings)
  endif
  Z3DEPS  = z3$(Z3VERSION)prover.cmx verifastPluginZ3$(Z3VERSION).ml
  ifeq ($(OS), Cygwin)
    Z3CCOPTS=
    LDLPATH=$(Z3)/bin
    Z3_OCAML=$(shell cygpath -m $(Z3)/ocaml)
  else
    # TODO: Specify these arguments when creating z3.cmxa; then you don't have to specify them here.
    Z3CCOPTS= \
            -ccopt "-I$(Z3)/ocaml -L$(Z3)/bin -L$(Z3)/lib" \
            -cclib -lz3-gmp -cclib -lz3stubs $(OCAMLLIB)/libcamlidl.a
    LDLPATH = $(Z3)/lib
    Z3_OCAML=$(Z3)/ocaml
  endif
  Z3ARGS  = -I $(Z3_OCAML) z3.cmxa z3$(Z3VERSION)prover.cmx verifastPluginZ3$(Z3VERSION).ml $(Z3CCOPTS)
  VERIFAST := $(LDLPATHVAR)=${LDLPATH}:$$$(LDLPATHVAR) ../bin/verifast
  Z3PRESENT=true
else
  VERIFAST := ../bin/verifast
  Z3PRESENT=false
endif

# Should Make print each commandline? Then use "make VERBOSE=yes".
ifndef VERBOSE
  .SILENT:
endif

ifeq ($(OS), Cygwin)
  DOTEXE=.exe
endif

# Paths
OCAML        = ${OCAMLBIN}/ocaml
# Note: the ".opt" version of the ocaml compiler is ~3.5x faster, but not
# available everywhere, so we autodetect whether we have it.
OCAMLC       = $(firstword $(wildcard ${OCAMLBIN}/ocamlc.opt ${OCAMLBIN}/ocamlc))
OCAMLOPT     = $(firstword $(wildcard ${OCAMLBIN}/ocamlopt.opt ${OCAMLBIN}/ocamlopt))
ifeq ($(OS), Cygwin)
  CAMLP4O    = camlp4o.opt
else
  CAMLP4O      = $(firstword $(wildcard ${OCAMLBIN}/camlp4o.opt ${OCAMLBIN}/camlp4o))
endif

# Do we build with "-I ./linux" or "-I ./win":
ifeq ($(OS), Cygwin)
  INCLUDE_OS_DIR = win
else
# Also for mac.
  INCLUDE_OS_DIR = linux
endif

# Number of CPUs
ifeq ($(OS), Darwin)
  NUMCPU ?= $(shell sysctl -n hw.ncpu)
else
# Works on Linux and Cygwin (Cygwin has no /sys).
  NUMCPU ?= $(shell cat /proc/cpuinfo | grep 'processor' | wc -l)
endif


env:
	@echo "Configuration:"
	@echo "---------------------"
	@echo "OS      : $(OS)"
	@echo "NUMCPU  : $(NUMCPU)"
	@echo "OCAMLBIN: $(OCAMLBIN)"
	@echo "OCAMLLIB: $(OCAMLLIB)"
	@echo "CWD     : $(CWD)"
	@echo "Z3      : $(Z3)"
	@echo "Z3V2    : $(Z3V2)"
	@echo "Z3V4    : $(Z3V4)"
	@echo "Z3DEPS  : $(Z3DEPS)"
	@echo "LDLPATH : $(LDLPATH)"
	@echo "WITHOUT_LABLGTK     : $(WITHOUT_LABLGTK)"
	@echo "GTKSOURCEVIEW_LFLAGS: $(GTKSOURCEVIEW_LFLAGS)"
	@echo "GTKSOURCEVIEW_LIBS  : ${GTKSOURCEVIEW_LIBS}"
	@echo "VERIFAST: ${VERIFAST}"


#------------------------------- Includes   ---------------------------------#
ifeq ($(OS), Linux)
  include linux/GNUmakefile
endif
ifeq ($(OS), Darwin)
  include linux/GNUmakefile
endif
ifeq ($(OS), Cygwin)
  include win/GNUmakefile
endif

include java_frontend/GNUmakefile

#------------------------------- Shorthands ---------------------------------#

SET_LDD = export CAML_LD_LIBRARY_PATH="$$CAML_LD_LIBRARY_PATH:$$GTKSOURCEVIEW_LIBS"
SET_ENV = export PATH="$(CWD)/../bin/:$(OCAMLBIN):$$PATH"; \
          export $(LDLPATHVAR)="$(LDLPATH):$$$(LDLPATHVAR)"

STDLIB = ../bin/crt.dll.vfmanifest
#sequence is important, it presents dependencies in command line of VeriFast
STDLIB_FILES_GEN = \
       ../bin/list.vfmanifest \
       ../bin/listex.vfmanifest \
       ../bin/raw_ghost_lists.vfmanifest \
       ../bin/arrays.vfmanifest \
       ../bin/quantifiers.vfmanifest \
       ../bin/assoclist.vfmanifest \
       ../bin/permutations.vfmanifest
STDLIB_FILES = \
	../bin/crt.vfmanifest \
	$(STDLIB_FILES_GEN) \
	../bin/threading.vfmanifest \
	../bin/pthread.vfmanifest

TOOLS_EXCEPT_VFIDE = ../bin/mysh$(DOTEXE) ../bin/verifast$(DOTEXE) \
        ../bin/main_class$(DOTEXE) ../bin/java_card_applet$(DOTEXE) \
        ../bin/dlsymtool$(DOTEXE) ../bin/vfstrip$(DOTEXE)

TOOLS = $(TOOLS_EXCEPT_VFIDE) ../bin/vfide$(DOTEXE)


ifndef WITHOUT_LABLGTK
build: $(TOOLS) $(STDLIB) tabhunt vfversion_autogen vfconfig_autogen
else
build: $(TOOLS_EXCEPT_VFIDE) $(STDLIB) tabhunt vfversion_autogen
endif
.PHONY: build

distclean:: clean

#------------------------------- Build normal case --------------------------#

clean::
	@echo "  CLEAN    "

../bin/%$(DOTEXE): %.ml
	@echo "  OCAMLOPT " $*.cmi
	${OCAMLOPT} -o ../bin/$*$(DOTEXE) $*.ml
clean::
	rm -f $(TOOLS)

%.cmi: %.mli
	@echo "  OCAMLOPT " $@
	${OCAMLOPT} -I ./java_frontend -c $*.mli
clean::
	rm -f *.cmi

%.cmx: %.ml
	@echo "  OCAMLOPT " $@
	${OCAMLOPT}  -thread -c -w p -warn-error FSU -c -I ./$(INCLUDE_OS_DIR) \
	  -I ./java_frontend -pp ${CAMLP4O} nums.cmxa  $*.ml
clean::
	rm -f *.cmx
	rm -f *.o

# We have " || rm ..." such that in case verifast fails, we do not end
# up with an empty (and thus incorrect) .dll.vfmanifest file.
# We have "> $(STDLIB)" for bootstrapping the standard library: the
# .dll.vfmanifest gets loaded when creating .dll.vfmanifest, so it must
# be empty.
$(STDLIB): $(STDLIB_FILES)
	@echo "  >        " $@
	> $(STDLIB)
	@echo "  VERIFAST " $@
	${VERIFAST} -shared $(STDLIB_FILES) -emit_dll_vfmanifest \
	  -emit_dll_vfmanifest_as $@  || (rm -f $(STDLIB) ; false)
	
../bin/%.vfmanifest: ../bin/%.c ../bin/%.gh ../bin/verifast$(DOTEXE)
	$(SET_ENV); ../bin/verifast -c -emit_vfmanifest ../bin/$*.c
clean::
	rm -f $(STDLIB)
	rm -f $(STDLIB_FILES_GEN)

#------------------------------- Auto code generation -----------------------#
DynType.mli: ../examples/plugin/DynType.mli
	@echo "  CAT      " $@
	@cat generated_file_warning.txt ../examples/plugin/DynType.mli > DynType.mli
clean::
	rm -f DynType.mli

plugins.mli: ../examples/plugin/plugins.mli
	@echo "  CAT      " $@
	cat generated_file_warning.txt ../examples/plugin/plugins.mli > plugins.mli
clean::
	rm -f plugins.mli

plugins2.mli: ../examples/plugin/plugins2.mli
	@echo "  CAT      " $@
	cat generated_file_warning.txt ../examples/plugin/plugins2.mli > plugins2.mli
clean::
	rm -f plugins2.mli

ifeq ($(OS), Darwin)
Fonts.ml: Fonts_mac.ml
	@echo "  CAT      " $@
	cat generated_file_warning.txt Fonts_mac.ml > Fonts.ml
else
Fonts.ml: Fonts_default.ml
	@echo "  CAT      " $@
	cat generated_file_warning.txt Fonts_default.ml > Fonts.ml
endif
clean::
	rm -f Fonts.ml

vfversion_autogen:
	@echo "  OCAML    " generate_vfversion.ml
	${OCAML} generate_vfversion.ml $(Z3PRESENT)
.PHONY: vfversion_autogen
clean::
	rm -f vfversion.ml

VFCONFIG_CONTENT=let z3_present = $(Z3PRESENT)
vfconfig_autogen:
	if [ ! -e vfconfig.ml ] || [ "$$(cat vfconfig.ml)" != "$(VFCONFIG_CONTENT)" ]; then \
	  echo "$(VFCONFIG_CONTENT)" > vfconfig.ml ;\
	fi	
.PHONY: vfconfig_autogen 
clean::
	rm -f vfconfig.ml
	
# We only want to rebuild vfversion.ml and everything that depends on it
# when it actually changes. But make itself causes vfversion.ml to change,
# so make must reload its dependency graph at runtime.
# We can trick make into reloading its dependency graph by
# - having a dependency from the target that creates the file to an
#   included makefile, here "../GNUmakefile.settings"; and
# - having the dependencies to the autogenerated file explicitly
#   (i.e. not a pattern like "%.cmx: %.ml"), e.g. "vfconfig.cmx: vfconfig.ml".
#   Otherwise make does not seam to notice if this file gets created.
../GNUmakefile.settings: vfversion_autogen vfconfig_autogen

#------------------------------- Build special cases ------------------------#

tabhunt:
	@echo "  OCAML    " tabhunter.ml
	${OCAML} tabhunter.ml
.PHONY: tabhunt

../bin/mysh$(DOTEXE): Fonts.cmx vfconfig.cmx mysh.ml
	@echo "  OCAMLOPT " $@
	${OCAMLOPT} -thread -o ../bin/mysh$(DOTEXE) unix.cmxa threads.cmxa Fonts.cmx vfconfig.cmx mysh.ml
mysh: ../bin/mysh$(DOTEXE)
.PHONY: mysh

ifeq ($(OS), Darwin)
macos/GSourceView2.cmx: macos/GSourceView2.ml
	@echo "  OCAMLOPT " $@
	cd macos; ${OCAMLOPT} -c -I +lablgtk2 GSourceView2.ml
endif
clean::
	rm -f macos/*.cm* macos/*.o

../bin/vfide$(DOTEXE): Printexc_proxy.cmx vfversion.cmx proverapi.cmx util.cmx \
  stats.cmx lexer.cmx ast.cmx parser.cmx verifast0.cmx verifast1.cmx \
  assertions.cmx verify_expr.cmx verifast.cmx simplex.cmx redux.cmx \
  verifastPluginRedux.ml $(Z3DEPS) Fonts.cmx $(GTKSOURCEVIEW_DEPS) \
  $(INCLUDE_OS_DIR)/Perf.cmxa vfide.ml
ifndef WITHOUT_LABLGTK
	@echo "  OCAMLOPT " $@
	$(SET_LDD); ${OCAMLOPT} -warn-error F -pp ${CAMLP4O} -o ../bin/vfide	\
	  -I +lablgtk2 lablgtk.cmxa $(GTKSOURCEVIEW_LFLAGS) gtkInit.cmx unix.cmxa \
	  nums.cmxa -I ./$(INCLUDE_OS_DIR) -I java_frontend Perf.cmxa proverapi.cmx \
	  Printexc_proxy.cmx vfversion.cmx dynlink.cmxa DynType.cmx plugins.cmx \
	  plugins_private.cmx plugins2.cmx util.cmx stats.cmx lexer.cmx ast.cmx \
	  parser.cmx ${JAVA_FE_INCLS} verifast0.cmx verifast1.cmx assertions.cmx \
	  verify_expr.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml \
	  $(Z3ARGS) Fonts.cmx vfide.ml
endif
ifneq ($(OS), Cygwin)
  ../bin/vfide$(DOTEXE): linux/libPerf_cobjs.a
endif
vfide: ../bin/vfide$(DOTEXE) $(STDLIB)
.PHONY: vfide

../bin/verifast$(DOTEXE): vfversion.cmx proverapi.cmx util.cmx stats.cmx lexer.cmx \
  ast.cmx parser.cmx verifast0.cmx verifast1.cmx assertions.cmx \
  verify_expr.cmx verifast.cmx simplex.cmx redux.cmx verifastPluginRedux.ml \
  $(Z3DEPS) SExpressions.cmx SExpressionEmitter.cmx \
  $(INCLUDE_OS_DIR)/Perf.cmxa vfconsole.ml
	@echo "  OCAMLOPT " $@
	${OCAMLOPT} -warn-error F -pp ${CAMLP4O} -o ../bin/verifast$(DOTEXE) unix.cmxa \
	  nums.cmxa -I ./$(INCLUDE_OS_DIR) -I ./java_frontend Perf.cmxa proverapi.cmx \
	  vfversion.cmx dynlink.cmxa DynType.cmx plugins.cmx plugins_private.cmx \
	  plugins2.cmx util.cmx stats.cmx lexer.cmx ast.cmx parser.cmx \
	  ${JAVA_FE_INCLS} verifast0.cmx verifast1.cmx assertions.cmx \
	  verify_expr.cmx verifast.cmx simplex.cmx redux.cmx \
	  verifastPluginRedux.ml $(Z3ARGS) SExpressions.cmx \
	  SExpressionEmitter.cmx vfconsole.ml
ifneq ($(OS), Cygwin)
  ../bin/verifast$(DOTEXE): linux/libPerf_cobjs.a
endif
verifast: ../bin/verifast$(DOTEXE) $(STDLIB)
.PHONY: verifast

z3prover.cmx: $(INCLUDE_OS_DIR)/Perf.cmx proverapi.cmx z3prover.ml
	@echo "  OCAMLOPT " $@
	${OCAMLOPT} -warn-error F -c -I $(Z3_OCAML) z3.cmxa -I ./$(INCLUDE_OS_DIR) Perf.cmx proverapi.cmx z3prover.ml

z3v2prover.cmx: $(INCLUDE_OS_DIR)/Perf.cmx proverapi.cmx z3v2prover.ml
	@echo "  OCAMLOPT " $@
	${OCAMLOPT} -warn-error F -c -I $(Z3_OCAML) z3.cmxa -I ./$(INCLUDE_OS_DIR) Perf.cmx proverapi.cmx z3v2prover.ml

z3v4prover.cmx: $(INCLUDE_OS_DIR)/Perf.cmx proverapi.cmx z3v4prover.ml
	@echo "  OCAMLOPT " $@
	${OCAMLOPT} -warn-error F -c -I $(Z3_OCAML) z3.cmxa -I ./$(INCLUDE_OS_DIR) Perf.cmx proverapi.cmx z3v4prover.ml

#------------------------------- Tests --------------------------------------#
test_plugin: verifast
	$(SET_ENV); \
	  ${MAKE} -C ../examples/plugin clean OCAMLOPT=${OCAMLOPT}
	$(SET_ENV); \
	  ${MAKE} -C ../examples/plugin all OCAMLOPT=${OCAMLOPT}
.PHONY: test_plugin

testsuite: $(STDLIB) $(TOOLS_EXCEPT_VFIDE)
	@echo "  MYSH     " testsuite
	$(SET_ENV); \
        cd ..; bin/mysh -cpus $(NUMCPU) < testsuite.mysh
.PHONY: testsuite

test: testsuite test_plugin 
.PHONY: test

#------------------------------- Dependencies -------------------------------#
vfversion.cmi: vfversion.mli
vfversion.cmo: vfversion.cmi	
vfversion.cmx: vfversion.cmi vfversion.ml
vfconfig.cmx: vfconfig.ml
mynum.cmx: mynum.ml
DynType.cmx: DynType.cmi DynType.ml
plugins.cmi: DynType.cmi plugins.mli
plugins.cmx: DynType.cmx plugins.cmi plugins.ml
plugins_private.cmx: plugins.cmx plugins_private.ml
plugins2.cmi: plugins.cmi plugins2.mli
plugins2.cmx: plugins_private.cmx plugins2.cmi plugins2.ml
util.cmx: $(INCLUDE_OS_DIR)/Perf.cmxa vfversion.cmi proverapi.cmx plugins2.cmx util.ml
stats.cmx: util.cmx stats.ml
lexer.cmx: stats.cmx lexer.ml
ast.cmx: lexer.cmx ast.ml
parser.cmx: ast.cmx parser.ml
verifast0.cmx: parser.cmx verifast0.ml java_frontend
verifast1.cmx: verifast0.cmx verifast1.ml
assertions.cmx: verifast1.cmx assertions.ml
verify_expr.cmx: assertions.cmx verify_expr.ml
verifast.cmx: verify_expr.cmx verifast.ml
verifast.cmo: vfversion.cmi proverapi.cmo verifast.ml
simplex.cmo: simplex.ml
proverapi.cmo: proverapi.ml
redux.cmo: proverapi.cmo simplex.cmo redux.ml
SExpressions.cmi: SExpressions.mli
SExpressions.cmx: SExpressions.cmi SExpressions.ml
SExpressionEmitter.cmi: verifast.cmx SExpressionEmitter.mli
SExpressionEmitter.cmx: verifast.cmx SExpressionEmitter.cmi SExpressions.cmx SExpressionEmitter.ml
proverapi.cmx: proverapi.ml
simplex.cmi: simplex.mli
simplex.cmx: $(INCLUDE_OS_DIR)/Perf.cmx simplex.cmi simplex.ml
redux.cmx: $(INCLUDE_OS_DIR)/Perf.cmx proverapi.cmx simplex.cmx redux.ml

# You can try building dependencies automatically, e.g. with
# $(OCAMLDEP) -pp ${CAMLP4O} -native -I . -I linux/ -I java_frontend \
#   $(filter-out pa_verifast.ml, $(wildcard *.ml)) *.mli linux/*.ml \
#   linux/*.mli java_frontend/*.ml java_frontend/*.mli > .depend
# but this does not seem to catch them all. Ocamlbuild manages to
# do it automatically, so it must be possible somehow.

#------------------------------- Release ------------------------------------#
release: release_core
release_core: test build
ifeq ($(OS), Cygwin)
	$(error Cygwin currently not supported for release)
endif
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

