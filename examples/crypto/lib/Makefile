#Compiler stuff
#--------------

CC = clang
AR = ar
# DEBUG += -g -D DEBUG

CFLAGS += -I include 
CFLAGS += -I polarssl/include

#Output
#------

LIB = libdolevyao.a

#Targets
#-------

all: lib

switch:
	cd include; \
	./switch_primitives.py;

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

lib: switch polar src/dolevyao.c
	$(CC) $(DEBUG) $(CFLAGS) -c -o src/dolevyao.o src/dolevyao.c;
	$(CC) $(DEBUG) $(CFLAGS) -c -o src/attacker.o src/attacker.c;
	ar rcs $(LIB) src/attacker.o src/dolevyao.o

tests: lib
	make -C tests

clean:
	make -C tests clean
	rm -f dolevyao.a
	rm -f src/*.o
	rm -f include/switch_primitives.gh
