CC ?= gcc
CFLAGS += -Wall

all: run

build: dll1_source1.o dll1_source2.o dll2_source.o
	gcc -shared -o libdll2.so dll2_source.o
	gcc -shared -o libdll1.so dll1_source1.o dll1_source2.o
	gcc main.c libdll1.so libdll2.so -o main

run: build
	./main

clean:
	rm -f *.o *.so main
