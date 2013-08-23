
ifdef BYTECODE
  PERF_OUT=Perf.cma
else
  PERF_OUT=Perf.cmxa
endif

ifdef DEBUG
  OCAMLC_DEBUG_FLAG = -g
endif

all:
	${OCAMLOPTOPT} $(OCAMLC_DEBUG_FLAG) -c caml_stopwatch.c
	ar rcs libPerf_cobjs.a caml_stopwatch.o
	${OCAMLOPTOPT} $(OCAMLC_DEBUG_FLAG) -a -o $(PERF_OUT) Perf.ml Stopwatch.mli -cclib -lPerf_cobjs

clean:
	rm -f *.a *.o *.cm*

