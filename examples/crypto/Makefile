#Compiler stuff
#--------------

CC = clang
AR = ar

CFLAGS += -I include
CFLAGS += -I polarssl/include
# CFLAGS += -D DEBUG

#Input
#-----

MODULES = \
  general \
  debug \
  principals \
  item \
  serialization \
  data_item \
  pair_item \
  nonce_item \
  key_item \
  hmac_item \
  encrypted_item \
  symmetric_encryption \
  asymmetric_encryption \
  encryption \
  network \
  cryptolib \
  attacker \

SOURCES = $(foreach module,$(MODULES),src/$(module).c)
OBJECTS = $(foreach module,$(MODULES),src/$(module).o)

#Output
#------

LIB = libcryptolib.so

#Targets
#-------

all : lib bin/cryptolib.dll.vfmanifest tests example_protocols

verify :
	verifast -shared -allow_assume bin/libpolarssl.so $(SOURCES)

bin/cryptolib.dll.vfmanifest : $(SOURCES)
	verifast -shared -allow_assume -emit_dll_vfmanifest \
	         -emit_dll_vfmanifest_as bin/cryptolib.dll.vfmanifest \
	         bin/libpolarssl.so $(SOURCES)
	

include/aux_include/switch_primitives.gh : tools/switch_primitives.py
	cd tools; \
	./switch_primitives.py; \
	mv switch_primitives.gh ../include/aux_include

switch_primitives : include/aux_include/switch_primitives.gh

polar :
	test -d polarssl || git clone https://github.com/polarssl/polarssl.git polarssl
	cd polarssl; \
	git checkout .; \
	git pull; \
	sed -i 's/\/\/#define POLARSSL_HAVEGE_C/#define POLARSSL_HAVEGE_C/g' \
	  include/polarssl/config.h; \
	sed -i 's/\/\/#define POLARSSL_RSA_C/#define POLARSSL_RSA_C/g' \
	  include/polarssl/config.h; \
	sed -i 's/\/\/#define POLARSSL_PK_PARSE_C/#define POLARSSL_PK_PARSE_C/g' \
	  include/polarssl/config.h; \
	sed -i 's/\/\/#define POLARSSL_PK_WRITE_C/#define POLARSSL_PK_WRITE_C/g' \
	  include/polarssl/config.h; \
	sed -i 's/\/\/#define POLARSSL_PEM_WRITE_C/#define POLARSSL_PEM_WRITE_C/g' \
	  include/polarssl/config.h; \
	sed -i 's/\/\/#define POLARSSL_THREADING_C/#define POLARSSL_THREADING_C/g' \
	  include/polarssl/config.h; \
	sed -i 's/\/\/#define POLARSSL_THREADING_PTHREAD/#define POLARSSL_THREADING_PTHREAD/g' \
	  include/polarssl/config.h; \
	make -j4;

include/aux_include/polarssl_sizes.h : tools/polarssl_sizes.c
	cd tools; \
	gcc -I ../polarssl/include/polarssl/ polarssl_sizes.c -lpthread -L ../polarssl/library -lpolarssl ; \
	./a.out; \
	rm a.out; \
	mv polarssl_sizes.h ../include/aux_include;

polar_sizes : polar include/aux_include/polarssl_sizes.h

lib : switch_primitives polar polar_sizes $(OBJECTS)
	gcc -shared $(OBJECTS) -o bin/$(LIB)

tests : lib
	make -C tests

example_protocols : bin/cryptolib.dll.vfmanifest lib
	make -C protocols

clean :
	rm -f bin/$(LIB)
	rm -f src/*.o
	rm -f bin/cryptolib.dll.vfmanifest
	make -C tests clean
	make -C protocols clean
