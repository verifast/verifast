CC ?= gcc
CFLAGS += -Wall

all: run

build: dll_source1.o dll_source2.o
	gcc -shared -o libdll2.so dll_source1.o
	gcc -shared -o libdll1.so dll_source2.o
	gcc main.c libdll1.so libdll2.so -o main
	gcc main2.c libdll1.so libdll2.so -o main2
	gcc main2.c libdll1.so libdll2.so -o main3
	gcc main2.c libdll1.so libdll2.so -o main4

run: build
	./main
	./main2
	./main3
	./main4

clean:
	rm -f *.o *.so main main2 main3 main4
