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
	@echo "  make test : run tests and examples"
	@echo "  make      : compile all and run tests"
	@echo "  make clean: remove output and temp files"
	@echo "  make build-cxx-ast-exporter: compile the C++ AST exporter tool"
	@echo ""
	@echo "Tips:"
	@echo "- Use e.g. 'make build VERBOSE=yes' to see more."
	@echo "- Use e.g. 'make build -j 4' to use 4 cores."
	@echo "- Use e.g. 'make ANNOT=yes' to output .annot files containing"
	@echo "- Use e.g. 'make BINANNOT=yes' to output .cmt and .cmti files containing"
	@echo "  type information."
	@echo "- To see stack trace, launch with 'OCAMLRUNPARAM=b verifast <args>'."
.PHONY: help

#------------------------------- Settings -----------------------------------#

-include ../GNUmakefile.settings

clean::
	-rm -Rf _build

# Note: OS is defined by the operating system as Windows_NT on Windows.
ifeq ($(OS), Linux)
else ifeq ($(OS), Darwin)
else ifeq ($(OS), Windows_NT)
else
  ifeq ($(shell uname -s), Linux)
          OS = Linux
  else ifeq ($(shell uname -s), Darwin)
          OS = Darwin
  else ifeq ($(shell uname -o), Cygwin)
          OS = Windows_NT
  else
          $(error "Could not recognize your platform")
  endif
endif

ifeq ($(OS), Linux)
  PLATFORM = Linux
else ifeq ($(OS), Darwin)
  PLATFORM = MacOS
else ifeq ($(OS), Windows_NT)
  PLATFORM = Windows
endif

# Lablgtk configuration
ifndef WITHOUT_LABLGTK
  LABLGTK_PATH ?= $(shell ocamlfind query lablgtk2)
  LABLGTK_FLAGS_ += -I $(LABLGTK_PATH)
  LABLGTK_FLAGS  += ${LABLGTK_FLAGS_} lablgtk.cmxa
  ifdef WITHOUT_GTKSOURCEVIEW
    GTKSOURCEVIEW_LFLAGS += -I macos GSourceView2.cmx GLineMarks.cmx
    GTKSOURCEVIEW_DEPS   += macos/GSourceView2.cmx macos/GLineMarks.cmx
  else
    GTKSOURCEVIEW_LFLAGS += -I linemarks lablgtksourceview2.cmxa linemarks.cmxa
    GTKSOURCEVIEW_LIBS   += ${LABLLIBS}
    ifeq ($(OS), Darwin)
      GTKSOURCEVIEW_DEPS   += ../lib/libgtksourceview-2.0.0.dylib
    endif
  endif
endif

ifeq ($(OS), Windows_NT)
  LDLPATHVAR=PATH
else
  LDLPATHVAR=LD_LIBRARY_PATH
endif

Z3V4DOT5=yes

# Z3 configuration
# TODO: refactor variable names: "Z3" could be anything (path? version? boolean?)
ifndef NOZ3
  ifdef Z3V4DOT5
    Z3VERSION = v4dot5
    Z3 = $(Z3V4DOT5)
  else
    NOZ3=1
  endif
endif
Z3V4DOT5PRESENT=false
ifdef Z3V4DOT5
  # It's Z3 when installed using `make install` and z3 when installed using OPAM
  Z3_OCAML ?= $(shell ocamlfind query -qe Z3)
  ifeq ($(Z3_OCAML),)
    Z3_OCAML := $(shell ocamlfind query z3)
    Z3_DLL_DIR ?= $(Z3_OCAML)
  else
    Z3_DLL_DIR ?= $(Z3_OCAML)/../..
  endif
  ifeq ($(OS), Darwin)
    Z3DEPS := $(Z3DEPS) ../lib/libz3.dylib
  else ifeq ($(OS), Windows_NT)
    Z3DEPS := $(Z3DEPS) ../bin/libz3.dll
  else ifeq ($(OS), Linux)
    Z3DEPS := $(Z3DEPS) ../bin/libz3.so
  endif
  Z3CCOPTS = -cclib "-L $(Z3_DLL_DIR)"
  Z3ARGS_EARLY = -I $(Z3_OCAML) z3ml.cmxa z3$(Z3VERSION)prover.cmx verifastPluginZ3$(Z3VERSION).ml verifastPluginReduxZ3$(Z3VERSION).ml  verifastPluginZ3$(Z3VERSION)Smtlib.ml $(Z3CCOPTS)
  ifeq ($(OS), Windows_NT)
    Z3_DLL_DEPS_DIR:=/usr/x86_64-w64-mingw32/sys-root/mingw/bin
    LDLPATH:=$(shell pwd)/../bin
    VERIFAST := $(LDLPATHVAR)=${LDLPATH}:$$$(LDLPATHVAR) ../bin/verifast
  else ifeq ($(OS), Darwin)
    LDLPATH:=$(Z3_DLL_DIR)
    VERIFAST := $(LDLPATHVAR)=${LDLPATH}:$$$(LDLPATHVAR) ../bin/verifast
  else
    VERIFAST := ../bin/verifast
  endif
  Z3PRESENT=false
  Z3V4DOT5PRESENT=true
else ifndef NOZ3
  Z3DEPS  = z3$(Z3VERSION)prover.cmx verifastPluginZ3$(Z3VERSION).ml
  ifeq ($(OS), Windows_NT)
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

export Z3_DLL_DIR

clean::
	rm -Rf ../lib
	-rm -f ../bin/libz3.dll

../lib/libgtksourceview-2.0.0.dylib:
	mkdir -p ../lib
	for i in $$( cat vfide-osx-local-dlls.txt ); do cp $$i ../lib; done
	mkdir -p ../lib/gdk-pixbuf-2.0/2.10.0
	echo > ../lib/gdk-pixbuf-2.0/2.10.0/loaders.cache

../bin/libz3.dll:
	cp $(Z3_DLL_DIR)/libz3.dll $(Z3_DLL_DEPS_DIR)/libwinpthread-1.dll $(Z3_DLL_DEPS_DIR)/libgomp-1.dll $(Z3_DLL_DEPS_DIR)/libgcc_s_seh-1.dll ../bin

../bin/libz3.so:
	cp $(Z3_DLL_DIR)/libz3.so ../bin

../lib/libz3.dylib:
	mkdir -p ../lib
	cp $(Z3_DLL_DIR)/libz3.dylib ../lib

# Should Make print each commandline? Then use "make VERBOSE=yes".
ifndef VERBOSE
  .SILENT:
endif

ifeq ($(OS), Windows_NT)
  DOTEXE=.exe
endif

# Paths
OCAMLBIN    ?= $(shell dirname `which ocamlc`)
OCAMLLIB    ?= $(shell ${OCAMLBIN}/ocamlc -where)
OCAML        = ${OCAMLBIN}/ocaml
# Note: the ".opt" version of the ocaml compiler is ~3.5x faster, but not
# available everywhere, so we autodetect whether we have it.
OCAMLC       = $(firstword $(wildcard ${OCAMLBIN}/ocamlc.opt ${OCAMLBIN}/ocamlc))
OCAMLOPT     = $(firstword $(wildcard ${OCAMLBIN}/ocamlopt.opt ${OCAMLBIN}/ocamlopt))

# Do we build with "-I ./linux" or "-I ./win":
ifeq ($(OS), Windows_NT)
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

# Variable $OCAMLCFLAGS specifies options for the optimizing native code
# compiler `ocamlopt`.
#
# Always include debug information. This seems necessary to prevent vfide
# crashes on OS X (see https://dnetcode.cs.kuleuven.be/issues/1975). Also, this
# is necessary to get stack traces.
OCAMLCFLAGS += -g -w p -warn-error +F+S+U
ifeq ($(OS), Linux)
  # See https://github.com/verifast/verifast/issues/145
  OCAMLCFLAGS += -runtime-variant _pic
endif
ifdef ANNOT
  OCAMLCFLAGS += -annot
endif
ifdef BINANNOT
  OCAMLCFLAGS += -bin-annot
endif

CWD ?= $(CURDIR)

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
	@echo "SET_ENV : ${SET_ENV}"


#------------------------------- Includes   ---------------------------------#
include java_frontend/GNUmakefile

# Path variables, for (de)serialization between C++/Rust and Ocaml,
# that are assumed to live in specific location in the vfdeps package.
# However, one can pass them to this makefile in order to override them (in case they exist in other locations).
ifdef CAPNP_BIN
	export CAPNP_BIN
endif 
ifdef CAPNP_INCLUDE
	export CAPNP_INCLUDE
endif
ifdef CAPNP_LIBS
	export CAPNP_LIBS
endif
include cxx_frontend/Makefile

clean::
	cd java_frontend; make clean; cd ..

# Rust frontend component
RUST_FE_DIR = rust_frontend
export RUST_FE_DIR
include $(RUST_FE_DIR)/Makefile

#------------------------------- Shorthands ---------------------------------#

SET_LDD    = export CAML_LD_LIBRARY_PATH="$$CAML_LD_LIBRARY_PATH:$$GTKSOURCEVIEW_LIBS"
SET_ENV    = export PATH="$(CWD)/../bin/:$(OCAMLBIN):$$PATH"; \
             export $(LDLPATHVAR)="$(LDLPATH):$$$(LDLPATHVAR)"
COMPILE    = ocamlfind ocamlopt $(OCAMLCFLAGS) -package ppx_parser,camlp-streams
COMPILE_BC = ocamlfind ocamlc $(OCAMLCFLAGS) -package ppx_parser,camlp-streams

STDLIB = ../bin/crt.dll.vfmanifest
#sequence is important, it presents dependencies in command line of VeriFast
STDLIB_FILES_GEN = \
       ../bin/list.vfmanifest \
       ../bin/listex.vfmanifest \
       ../bin/raw_ghost_lists.vfmanifest \
       ../bin/strong_ghost_lists.vfmanifest \
       ../bin/arrays.vfmanifest \
       ../bin/quantifiers.vfmanifest \
       ../bin/assoclist.vfmanifest \
       ../bin/bitops.vfmanifest \
       ../bin/permutations.vfmanifest
STDLIB_FILES = \
	../bin/crt.vfmanifest \
	$(STDLIB_FILES_GEN)

TOOLS_EXCEPT_VFIDE = ../bin/mysh$(DOTEXE) ../bin/verifast$(DOTEXE) \
        ../bin/main_class$(DOTEXE) ../bin/java_card_applet$(DOTEXE) \
        ../bin/dlsymtool$(DOTEXE) ../bin/vfstrip$(DOTEXE) ../bin/explorer$(DOTEXE)

TOOLS_EXCEPT_VFIDE += ../bin/vf-cxx-ast-exporter$(DOTEXE) build-vf-rust-mir-exporter

TOOLS = $(TOOLS_EXCEPT_VFIDE) ../bin/vfide$(DOTEXE)

vf: ../bin/verifast$(DOTEXE) ../bin/vfide$(DOTEXE)

ifndef WITHOUT_LABLGTK
build: $(TOOLS) $(STDLIB) tabhunt
else
build: $(TOOLS_EXCEPT_VFIDE) $(STDLIB) tabhunt
endif
.PHONY: build

# Only builds the C++ AST exporter tool binary (which checks macro expansions and serializes the C++ AST).
# No need to use this target if you're working on (the C++ support of VeriFast) itself.
# Only required if you worked on the C++ AST exporter tool, or edited the capnp serialization schema.
build-cxx-ast-exporter: ../bin/vf-cxx-ast-exporter$(DOTEXE)
.PHONY: build-cxx-ast-exporter

distclean:: clean

INCLUDES = -I java_frontend -I shape_analysis -I cxx_frontend -I $(RUST_FE_DIR)

#------------------------------- Build normal case --------------------------#

clean::
	@echo "  CLEAN    "

../bin/%$(DOTEXE): %.ml
	@echo "  OCAMLOPT " $*.cmi
	$(COMPILE) -o ../bin/$*$(DOTEXE) $*.ml
clean::
	rm -f $(TOOLS)

%.cmi: %.mli
	@echo "  OCAMLOPT " $@
	$(COMPILE) $(INCLUDES) -c -package num,camlp-streams $*.mli
clean::
	rm -f *.cmi

%.cmx: %.ml $(INCLUDE_OS_DIR)/Perf.cmxa
	@echo "  OCAMLOPT " $@
	$(COMPILE) -thread -c -w p -warn-error +F+S+U -c $(INCLUDES) -package num,camlp-streams $*.ml
clean::
	rm -f *.cmx
	rm -f *.o

%.cmo: %.ml
	@echo "    OCAMLC " $@
	$(COMPILE_BC) -thread $(INCLUDES) -I $(Z3_OCAML) -o $@ -c $*.ml
clean::
	rm -f *.cmo
	cd java_frontend && rm -f *.cmo

clean::
	rm -f *.annot

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
../bin/bitops.vfmanifest: ../bin/bitops.c ../bin/bitops.gh ../bin/verifast$(DOTEXE)
	$(SET_ENV); ../bin/verifast -c -prover z3v4.5 -emit_vfmanifest ../bin/bitops.c
clean::
	rm -f $(STDLIB)
	rm -f $(STDLIB_FILES_GEN)

#------------------------------- Build special cases ------------------------#

tabhunt:
	@echo "  OCAML    " tabhunter.ml
	${OCAML} tabhunter.ml
.PHONY: tabhunt

.FORCE:
.PHONY: .FORCE

_build/default/mysh/mysh.exe: .FORCE
	@echo "  DUNE " $@
	dune build mysh/mysh.exe

../bin/mysh$(DOTEXE): _build/default/mysh/mysh.exe
	if [ ! -e $@ -o $< -nt $@ ]; then cp -f $< $@; fi

mysh: ../bin/mysh$(DOTEXE)
.PHONY: mysh

_build/default/dlsymtool/dlsymtool.exe: .FORCE
	@echo "  DUNE " $@
	dune build $@

../bin/dlsymtool$(DOTEXE): _build/default/dlsymtool/dlsymtool.exe
	if [ ! -e $@ -o $< -nt $@ ]; then cp -f $< $@; fi

_build/default/main_class/main_class.exe: .FORCE
	@echo "  DUNE " $@
	dune build $@

../bin/main_class$(DOTEXE): _build/default/main_class/main_class.exe
	if [ ! -e $@ -o $< -nt $@ ]; then cp -f $< $@; fi

_build/default/java_card_applet/java_card_applet.exe: .FORCE
	@echo "  DUNE " $@
	dune build $@

../bin/vfstrip$(DOTEXE): _build/default/vfstrip/vfstrip.exe
	if [ ! -e $@ -o $< -nt $@ ]; then cp -f $< $@; fi

_build/default/vfstrip/vfstrip.exe: .FORCE
	@echo "  DUNE " $@
	dune build $@

../bin/java_card_applet$(DOTEXE): _build/default/java_card_applet/java_card_applet.exe
	if [ ! -e $@ -o $< -nt $@ ]; then cp -f $< $@; fi

ifndef WITHOUT_LABLGTK

VERIFAST_PLUGINS=Redux Cvc4 ExternalZ3 ReduxSmtlib

ifeq ($(OS), Darwin)
  OCAMLOPT_CCLIB_FLAGS += -Xlinker -headerpad_max_install_names
  OCAMLOPT_LINKFLAGS += -cclib "-Xlinker -headerpad_max_install_names"
else ifeq ($(OS), Linux)
  OCAMLOPT_CCLIB_FLAGS += -Wl,-rpath=$$ORIGIN
  OCAMLOPT_LINKFLAGS += -cclib -Wl,-rpath='$$ORIGIN'
else
  OCAMLOPT_CCLIB_FLAGS =
endif
export OCAMLOPT_CCLIB_FLAGS

../bin/vfide$(DOTEXE): _build/default/vfide/vfide.exe
	if [ ! -e $@ -o $< -nt $@ ]; then cp -f $< $@; fi
ifeq ($(OS), Darwin)
	DYLD_LIBRARY_PATH=../lib DYLD_PRINT_LIBRARIES=1 ../bin/vfide -verify_and_quit ../examples/busywaiting/ioliveness/echo_live_mt.c > vfide-libraries.log 2>&1
	! grep /usr/local vfide-libraries.log
endif

ifeq ($(OS), Windows_NT)
  PROJDIR:=$(shell cygpath -m `pwd`)
  export OCAMLPATH += ;$(PROJDIR)
else
  PROJDIR:=$(shell pwd)
  export OCAMLPATH += :$(PROJDIR)
endif

_build/default/vfide/vfide.exe: $(Z3DEPS) $(GTKSOURCEVIEW_DEPS) .FORCE
	@echo "  DUNE " $@
	$(SET_LDD); dune build $@

_build/default/linemarks/default/hello_vala/hello_vala.exe: .FORCE
	@echo "  DUNE " $@
	$(SET_LDD); dune build $@

_build/default/linemarks/default/hello_vala/hello_vala_ml.exe: .FORCE
	@echo "  DUNE " $@
	$(SET_LDD); dune build $@

hello_vala: _build/default/linemarks/default/hello_vala/hello_vala.exe
hello_vala_ml: _build/default/linemarks/default/hello_vala/hello_vala_ml.exe
.PHONY: hello_vala hello_vala_ml
endif
vfide: ../bin/vfide$(DOTEXE) $(STDLIB)
.PHONY: vfide

_build/default/vfconsole/vfconsole.exe: $(Z3DEPS) .FORCE
	@echo "  DUNE " $@
	dune build $@

../bin/verifast$(DOTEXE): _build/default/vfconsole/vfconsole.exe
	if [ ! -e $@ -o $< -nt $@ ]; then cp -f $< $@; fi
ifeq ($(OS), Darwin)
	install_name_tool -change libz3.dylib @executable_path/../lib/libz3.dylib ../bin/verifast
endif

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# This section is specifically related to bytecode compilation. Currently, it is
# a bit self-contained to avoid potentially breaking changes to the rest of the
# Makefile. It has only been tested on macOS with a local OPAM switch.

# Explicit specification of objects in order.
#
# It would be better to share usage of this list with the optimized Verifast
# target `../bin/verifast$(DOTEXE)`.
VERIFAST_BC_OBJECTS = \
	proverapi.cmo util.cmo ast.cmo stats.cmo lexer.cmo parser.cmo \
	$(JAVA_FE_DEPS:.cmx=.cmo) \
	verifast0.cmo verifast1.cmo assertions.cmo \
	verify_expr.cmo verifast.cmo simplex.cmo redux.cmo combineprovers.cmo \
	smtlib.cmo smtlibprover.cmo \
	$(VERIFAST_PLUGINS:%=verifastPlugin%.cmo) \
	z3v4dot5prover.cmo \
	verifastPluginZ3v4dot5.cmo verifastPluginReduxZ3v4dot5.cmo  verifastPluginZ3v4dot5Smtlib.cmo  \
	json.cmo vfconsole.cmo

# Looking for dependency directories in the local OPAM installation.
INCLUDE_DIR_NUM = $(shell ocamlfind query num)
INCLUDE_DIR_THREADS = $(shell ocamlfind query threads)/threads
INCLUDE_DIR_Z3 = $(shell ocamlfind query z3)
INCLUDE_DIR_ZARITH = $(shell ocamlfind query zarith)
VERIFAST_BC_INCLUDES = -I $(INCLUDE_DIR_NUM) -I $(INCLUDE_DIR_THREADS) -I $(INCLUDE_DIR_Z3) -I $(INCLUDE_DIR_ZARITH)
# Included for the optimized target(s), but not necessary?
# -I src \
# -I src/java_frontend \
# -I src/shape_analysis \
# -I $(INCLUDE_DIR_OS) 

# As I said: only tested on macOS.
../bin/verifast.bc: linux/Perf.cma $(VERIFAST_BC_OBJECTS)
	@echo "    OCAMLC " $@
	$(COMPILE_BC) $(OCAMLOPT_LINKFLAGS) -warn-error F -o $@ \
		$(VERIFAST_BC_INCLUDES) \
		threads.cma z3ml.cma linux/Perf.cma \
		$(VERIFAST_BC_OBJECTS)
clean::
	rm -f ../bin/verifast.bc

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

_build/default/explorer/explorer.exe: .FORCE
	@echo "  DUNE " $@
	dune build $@

../bin/explorer$(DOTEXE): _build/default/explorer/explorer.exe
	if [ ! -e $@ -o $< -nt $@ ]; then cp -f $< $@; fi

verifast: ../bin/verifast$(DOTEXE) $(STDLIB)
.PHONY: verifast

z3v4dot5prover.cmx: $(INCLUDE_OS_DIR)/Perf.cmxa proverapi.cmx z3v4dot5prover.ml
	@echo "  OCAMLOPT " $@
	$(COMPILE) -warn-error F -c -I $(Z3_OCAML) -I ./$(INCLUDE_OS_DIR) -package num Perf.cmxa proverapi.cmx z3v4dot5prover.ml

clean::
	rm -f shape_analysis/*.cm[ix] shape_analysis/*.cmo

#------------------------------- Tests --------------------------------------#
testsuite: $(STDLIB) $(TOOLS_EXCEPT_VFIDE)
	@echo "  RUN " json_tests
	dune build json_tests/json_tests.exe
	dune exec json_tests/json_tests.exe
	@echo "  MYSH     " testsuite
	$(SET_ENV); \
        cd ..; bin/mysh -cpus $(NUMCPU) < testsuite.mysh
.PHONY: testsuite

clean::
	if [ -f ./json_tests$(DOTEXE) ]; then rm json_tests$(DOTEXE); fi

# Verify model solution of student assignments to prevent regression.
assignment_tests: $(STDLIB) $(TOOLS_EXCEPT_VFIDE)
	@echo "  MYSH     " assignments/run_model_solutions
	$(SET_ENV); \
        if [ -d ../assignments ]; then cd ../assignments; ../bin/mysh -cpus $(NUMCPU) < run_model_solutions.mysh; fi
.PHONY: assignment_tests

# Do not run the test targets in parallel because of GNU Make bug:
# If one of the parallel targets fails, make prints an error
# before the others stop. The other targets print (long) output after
# this error message. The user does not see the error and thinks
# the tests passed. (someone reported this years ago here:
# https://lists.gnu.org/archive/html/bug-make/2010-09/msg00033.html)
# So we serialize the test targets.
test: testsuite assignment_tests
.PHONY: test
testsuite: assignment_tests # dependency to enforce serialization

ifdef VERIFAST_JAVA_AST_SERVER
java_frontend_test: $(STDLIB) $(TOOLS_EXCEPT_VFIDE)
	@echo "  MYSH     " examples/java/frontend/frontend
	$(SET_ENV); \
	cd ../examples/java/frontend; ../../../bin/mysh -cpus $(NUMCPU) < frontend.mysh
.PHONY: java_frontend_test
test: java_frontend_test

assignment_test: java_frontend_tests # dependency to enforce serialization
endif

# Not all tests manage to always clean up (usually when interrupted),
# and not all tests provide a "make clean" themselves. So we clean here.
clean:: cleantest
cleantest::
	@echo "  CLEANTEST"
	rm -f ../examples/crypto/bin/cryptolib.dll.vfmanifest
	rm -f ../examples/java/chat/Member_.java
	rm -f ../examples/java/chat/chat_provide0.java
	rm -f ../examples/java/chat/chat_provide0_*.java
	rm -f ../examples/reduced_annotations/c_language/partially_annotated2.dll.vfmanifest
	rm -f ../examples/true
	rm -f ../examples/tso/cvm0_.c
	rm -f ../examples/tso/cvm0__.c
	rm -f ../examples/BeepDriver/BeepDriver_proxy.c
	rm -f ../examples/BeepDriver/BeepDriver_proxy.h
	rm -f ../examples/BeepDriver/BeepDriver_proxy.vfmanifest
	rm -f ../examples/a.out
	rm -f ../examples/java/Iterator/prog_provide0_*.java
	rm -f ../examples/java/"Java Card"/Addressbook_provide0_*.java
	rm -f ../examples/java/"Java Card"/Echo_provide0_*.java
	rm -f ../examples/java/"Java Card"/JavaCard_provide0_*.java
	rm -f ../examples/java/"Java Card"/NewEPurse/NewEPurseApplet_provide0_*.java
	rm -f ../examples/java/"Java Card"/NewJTicket/NewJTicketApplet_provide0_*.java
	rm -f ../examples/java/"Java Card"/Store_provide0_*.java
	rm -f ../examples/java/"Java Card"/shareable-applets/wallet_provide0_*.java
	rm -f ../examples/java/chatbot/Bot_provide0_*.java
	# Needs to be shipped, they are autogenerated with an ocaml script
	# and we do not want to depend on ocaml just to run the testsuite.
	#rm -f ../examples/helloproc/*autogenerated*
	rm -f ../examples/MockKernel/MockKernelModule_proxy*
	rm -f ../examples/java/"Java Card"/NewEidCard/EidCard-with-auto_provide0_*.java
	rm -f ../examples/java/"Java Card"/NewEidCard/EidCard_provide0_*.java

#------------------------------- Release ------------------------------------#

VFVERSION ?= $(shell git describe --always --dirty)
export VFVERSION

release: release_core
release_core:  build-cxx-ast-exporter test build
	rm -Rf verifast-$(VFVERSION); mkdir verifast-$(VFVERSION)
	strip ../bin/vf-cxx-ast-exporter$(DOTEXE)
	cp -R ../bin verifast-$(VFVERSION)
ifeq ($(OS), Windows_NT)
	cd $(GTK)/bin && cp -v \
    LIBFREETYPE-6.DLL \
    LIBINTL-8.DLL \
    LIBATK-1.0-0.DLL \
    LIBCAIRO-2.DLL \
    LIBEXPAT-1.DLL \
    LIBFONTCONFIG-1.DLL \
    LIBGDK-WIN32-2.0-0.DLL \
    LIBGDK_PIXBUF-2.0-0.DLL \
    LIBGIO-2.0-0.DLL \
    LIBGLIB-2.0-0.DLL \
    LIBGMODULE-2.0-0.DLL \
    LIBGOBJECT-2.0-0.DLL \
    LIBGTHREAD-2.0-0.DLL \
    LIBGTK-WIN32-2.0-0.DLL \
    LIBGTKSOURCEVIEW-2.0-0.DLL \
    LIBPANGO-1.0-0.DLL \
    LIBPANGOCAIRO-1.0-0.DLL \
    LIBPANGOFT2-1.0-0.DLL \
    LIBPANGOWIN32-1.0-0.DLL \
    LIBPNG14-14.DLL \
    LIBXML2-2.DLL \
    ZLIB1.DLL \
    $(CWD)/verifast-$(VFVERSION)/bin
	cd verifast-$(VFVERSION) && \
	mkdir etc && \
	cd etc && \
	mkdir gtk-2.0 && \
	cd gtk-2.0 && \
	echo "" > gdk-pixbuf.loaders && \
	echo 'gtk-theme-name = "MS-Windows"' > gtkrc && \
	cd .. && \
	cd .. && \
	mkdir -p share/themes/MS-Windows/gtk-2.0 && \
	cd share/themes/MS-Windows/gtk-2.0 && \
	cp $(GTK)/share/themes/MS-Windows/gtk-2.0/gtkrc . && \
	cd ../../../.. && \
	mkdir -p lib/gtk-2.0/2.10.0/engines && \
	cp $(GTK)/lib/gtk-2.0/2.10.0/engines/libwimp.dll lib/gtk-2.0/2.10.0/engines
endif
ifeq ($(OS), Linux)
	cp /usr/lib/x86_64-linux-gnu/libgtksourceview-2.0.so.0.0.0 verifast-$(VFVERSION)/bin/libgtksourceview-2.0.so.0
endif
ifeq ($(OS), Darwin)
	cd verifast-$(VFVERSION)/bin; mv vfide vfide-core
	cp vfide-mac.sh verifast-$(VFVERSION)/bin/vfide
	cp -R ../lib verifast-$(VFVERSION)
endif
	cp -R ../examples verifast-$(VFVERSION)
	cp -R ../help verifast-$(VFVERSION)
	cp -R ../javacard_tutorial verifast-$(VFVERSION)
	cp -R ../tests verifast-$(VFVERSION)
	cp -R ../tutorial_solutions verifast-$(VFVERSION)
	mkdir verifast-$(VFVERSION)/tutorial
	cd verifast-$(VFVERSION)/tutorial_solutions; for f in *.c; do ../bin/vfstrip < $$f > ../tutorial/$$f; done; cd ../..
	cp ../testsuite.mysh verifast-$(VFVERSION)
	echo "$(VFVERSION)" > verifast-$(VFVERSION)/bin/VERSION
	echo "$(VFVERSION) (released $(shell date +%Y-%m-%d))" >> verifast-$(VFVERSION)/bin/VERSION
ifeq ($(OS), Windows_NT)
	cp ../test.bat verifast-$(VFVERSION)
else
	cp ../test.sh verifast-$(VFVERSION)
endif

ifeq ($(OS), Darwin)
  RELEASE_SUFFIX=-osx
else
  RELEASE_SUFFIX=
endif

nightly: release
ifeq ($(OS), Windows_NT)
	printf "SHA-224 of release contents: "; cd verifast-$(VFVERSION); find . -type f ! -path ./bin/VERSION -print0 | sort -z | xargs -0 sha224sum | sha224sum
	rm verifast-nightly.zip || true
	7z a verifast-nightly.zip verifast-$(VFVERSION)
	ls -l verifast-nightly.zip
	sha224sum verifast-nightly.zip
else
	printf "SHA-224 of release contents: "; cd verifast-$(VFVERSION); find . -type f ! -path ./bin/VERSION -print0 | sort -z | xargs -0 shasum -a 224 | shasum -a 224
	rm -Rf ../upload || true
	mkdir ../upload || true
	tar czf ../upload/verifast-nightly$(RELEASE_SUFFIX).tar.gz verifast-$(VFVERSION)
	ls -l ../upload/verifast-nightly$(RELEASE_SUFFIX).tar.gz
	shasum -a 224 ../upload/verifast-nightly$(RELEASE_SUFFIX).tar.gz
endif
ifdef GITHUB_ENV
	echo "VFVERSION=$(VFVERSION)" >> $$GITHUB_ENV
	echo "VERIFAST_OS=$(OS)" >> $$GITHUB_ENV
endif
