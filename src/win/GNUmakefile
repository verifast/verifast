win/Perf.cmxa: win/caml_perf.c win/Perf.mli win/Perf.ml win/Stopwatch.mli win/caml_stopwatch.c
	cd win; ocamlopt.opt -c -opaque Stopwatch.mli Stopwatch.ml
	cd win; ocamlopt.opt -a -o Perf.cmxa caml_perf.c Perf.mli Perf.ml caml_stopwatch.c Stopwatch.cmx

clean::
	rm -f win/*.o win/*.a win/*.cm*
