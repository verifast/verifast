all: verif exec

verif:
	verifast -c -I sub1/sub2 -emit_vfmanifest main.c
	verifast -c -I sub1/ -emit_vfmanifest lib.c	
# 	verifast lib.o main.o LINKING CORRECTLY FAILS NOW

exec:
	gcc -c -I sub1/sub2 -emit_vfmanifest main.c
	gcc -c -I sub1/ -emit_vfmanifest lib.c	
	gcc lib.o main.o
	./a.out

tests: lib
	make -C tests

clean:
	rm -f a.out
	rm -f *.o
	rm -f *.vfmanifest
