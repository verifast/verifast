# You probably don't want to use this makefile, you probably want
# /src/GNUmakefile
# /src/GNUmakefile includes this one.


ifdef BYTECODE
  PERF_OUT=Perf.cma
else
  PERF_OUT=Perf.cmxa
endif

ifdef DEBUG
  OCAML_DEBUG_FLAG = -g
endif

all_src_linux: linux/caml_stopwatch.o linux/libPerf_cobjs.a linux/Perf.cmxa \
    linux/Perf.a linux/Perf.cmi linux/Perf.cmx linux/Stopwatch.cmi

linux/caml_stopwatch.o: linux/caml_stopwatch.c
	@echo "  OCAMLOPT " $@
	cd linux ; ${OCAMLOPT} $(OCAML_DEBUG_FLAG) -c caml_stopwatch.c

linux/libPerf_cobjs.a: linux/caml_stopwatch.o
	@echo "  AR       " $@
	cd linux ; ar rcs libPerf_cobjs.a caml_stopwatch.o

linux/Perf.cmxa: linux/Perf.ml linux/Stopwatch.mli
	@echo "  OCAMLOPT " $@
	cd linux ; ${OCAMLOPT} $(OCAML_DEBUG_FLAG) -a -o $(PERF_OUT) Perf.ml Stopwatch.mli -cclib -lPerf_cobjs

# These targets are actually also build when building linux/Perf.cmxa.
linux/Perf.a linux/Perf.cmi linux/Perf.cmx linux/Stopwatch.cmi: linux/Perf.cmxa

clean::
	rm -f linux/*.a linux/*.o linux/*.cm*

