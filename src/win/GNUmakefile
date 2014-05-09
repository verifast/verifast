win/Perf.cmxa: win/caml_perf.c win/Perf.mli win/Perf.ml win/Stopwatch.mli win/caml_stopwatch.c
	cd win; ocamlopt.opt -a -o Perf.cmxa caml_perf.c Perf.mli Perf.ml Stopwatch.mli caml_stopwatch.c

clean::
	rm -f win/*.o win/*.a win/*.cm*
