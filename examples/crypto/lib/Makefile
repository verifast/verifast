#Compiler stuff
#--------------

CC = clang
AR = ar

CFLAGS += -I include 
CFLAGS += -I polarssl/include
# CFLAGS += -g -D DEBUG

#Input
#-----

OBJECTS = \
  src/attacker.o \
  src/dolevyao.o 
  
#Output
#------

LIB = libdolevyao.so

#Targets
#-------

all: lib

switch_primitives:
	cd tools; \
	./switch_primitives.py; \
	mv switch_primitives.gh ../include

polar:
	test -d polarssl || git clone https://github.com/polarssl/polarssl.git polarssl
	cd polarssl; \
	git checkout .; \
	git pull; \
	sed -i 's/\/\/#define POLARSSL_HAVEGE_C/#define POLARSSL_HAVEGE_C/g' \
	  include/polarssl/config.h; \
	sed -i 's/\/\/#define POLARSSL_THREADING_PTHREAD/#define POLARSSL_THREADING_PTHREAD/g' \
	  include/polarssl/config.h; \
	sed -i 's/\/\/#define POLARSSL_THREADING_C/#define POLARSSL_THREADING_C/g' \
	  include/polarssl/config.h; \
	make -j4;

polar_sizes: tools/switch_primitives.py
	cd tools; \
	gcc -I ../polarssl/include/polarssl/ polarssl_sizes.c -lpthread -L ../polarssl/library -lpolarssl ; \
	./a.out; \
	rm a.out; \
	mv polarssl_sizes.h ../include;

dolevyao_dll: bin/dolevyao.vfmanifest
	../../../bin/verifast -shared bin/dolevyao.vfmanifest -emit_dll_vfmanifest

lib: switch_primitives polar polar_sizes dolevyao_dll $(OBJECTS)
	gcc -shared $(OBJECTS) -o bin/$(LIB)

tests: lib
	make -C tests

clean:
	make -C tests clean
	rm -f $(LIB)
	rm -f src/*.o
	rm -f include/switch_primitives.gh
