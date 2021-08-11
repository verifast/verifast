# You probably don't want to use this makefile, you probably want
# /src/GNUmakefile
# /src/GNUmakefile includes this one.

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

linux/Stopwatch.cmi: linux/Stopwatch.mli
	@echo "  OCAMLOPT " $@
	cd linux ; ${OCAMLOPT} -c Stopwatch.mli

linux/Stopwatch.cmx: linux/Stopwatch.ml linux/Stopwatch.cmi
	@echo "  OCAMLOPT " $@
	cd linux ; ${OCAMLOPT} -c Stopwatch.ml

linux/Perf.cmx: linux/Perf.ml
	@echo "  OCAMLOPT " $@
	cd linux ; ${OCAMLOPT} -c Perf.ml

linux/Perf.cmxa: linux/Perf.cmx linux/Stopwatch.cmi linux/Stopwatch.cmx linux/libPerf_cobjs.a
	@echo "  OCAMLOPT " $@
	cd linux ; ${OCAMLOPT} $(OCAML_DEBUG_FLAG) -a -o Perf.cmxa Stopwatch.cmx Perf.cmx -cclib -lPerf_cobjs

linux/Perf.cma: linux/Perf.cmo linux/Stopwatch.cmi linux/Stopwatch.cmo linux/caml_stopwatch.o 
	@echo "    OCAMLC " $@
	cd linux ; ${OCAMLC} $(OCAML_DEBUG_FLAG) -a -o Perf.cma -custom linux/caml_stopwatch.o Stopwatch.cmo Perf.cmo

clean::
	rm -f linux/*.a linux/*.o linux/*.cm*

