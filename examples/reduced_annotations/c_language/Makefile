CC = gcc -D EXECUTE

all: verify run

verify:
	mysh < verify.mysh

compile: 
	$(CC) -c -Wall -Werror -fpic partially_annotated2.c
	$(CC) -shared -o partially_annotated2.so partially_annotated2.o
	$(CC) main.c partially_annotated1.c partially_annotated2.so -o app

run: compile
	LD_LIBRARY_PATH=partially_annotated2.so:$LD_LIBRARY_PATH
	./app

clean:
	rm -f app
	rm -f partially_annotated2.o
	rm -f partially_annotated2.so
	rm -f partially_annotated2.dll.vfmanifest