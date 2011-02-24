all:
	ocamlopt.opt -c caml_stopwatch.c
	ar rcs libPerf_cobjs.a caml_stopwatch.o
	ocamlopt.opt -a -o Perf.cmxa Perf.ml Stopwatch.mli -cclib -lPerf_cobjs
