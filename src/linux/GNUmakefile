
all:
	${OCAMLOPTOPT} -c caml_stopwatch.c
	ar rcs libPerf_cobjs.a caml_stopwatch.o
	${OCAMLOPTOPT} -a -o Perf.cmxa Perf.ml Stopwatch.mli -cclib -lPerf_cobjs

clean:
	rm -f *.a *.o *.cm*

