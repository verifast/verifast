VERBOSE = -verbose -1
VF = ../../../bin/verifast $(VERBOSE)

include ../Makefile.include

MODULES = \
  auxiliary_definitions \
  polarssl \
  random \
  polarssl_attacker
OBJECTS   = $(foreach src,$(MODULES),src/$(addsuffix .o, $(src)))
MANIFESTS = $(foreach src,$(MODULES),src/$(addsuffix .vfmanifest, $(src)))

all: \
	library \
	annotated_api/polarssl_defines.h \
	bin/libann_polarssl.dll.vfmanifest \
	bin/libann_polarssl.so \
	example_protocols

library :
	$(call pprint_big_begin, Updating PolarSSL repository)
	@test -d polarssl_library || \
	  wget https://tls.mbed.org/download/polarssl-1.3.9-gpl.tgz; \
	  tar xvf polarssl-1.3.9-gpl.tgz; \
	  mv polarssl-1.3.9 polarssl_library; \
	  cd polarssl_library; \
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
	  sed -i 's/\/\/#define POLARSSL_MEMORY_DEBUG/#define POLARSSL_MEMORY_DEBUG/g' \
	    include/polarssl/config.h; \
	  sed -i 's/\/\/#define POLARSSL_MEMORY_BACKTRACE/#define POLARSSL_MEMORY_BACKTRACE/g' \
	    include/polarssl/config.h
	  make -C polarssl_library -j4;
	$(call pprint_big_end)

annotated_api/polarssl_defines.h : tools/polarssl_defines.c
	@cd tools; \
	  ${CC} -I ../polarssl_library/include/polarssl/ polarssl_defines.c \
	    -lpthread -L ../polarssl_library/library -lpolarssl ; \
	  ./a.out; \
	  rm a.out; \
	  mv polarssl_defines.h ../annotated_api;
	$(call pprint_big, Generated header with size and other defines for annotated PolarSSL library)

bin/libann_polarssl.dll.vfmanifest : bin/libann_polarssl.vfmanifest $(MANIFESTS)
	@${VF} -allow_assume -shared \
	  -emit_dll_vfmanifest -emit_dll_vfmanifest_as \
	  bin/libann_polarssl.dll.vfmanifest \
	  bin/libann_polarssl.vfmanifest \
	  $(MANIFESTS)
	$(call pprint_big, Link time verification of annotated PolarSSL library done)

bin/libann_polarssl.so : $(OBJECTS)
	@${CC} -shared $(OBJECTS) -o bin/libann_polarssl.so
	$(call pprint_big, Linked verified annotated PolarSSL library)

example_protocols:
	make -C protocols

clean:
	make -C protocols clean
	# To force recreation on next make, not removed because in VeriFast repo
	@touch tools/polarssl_defines.c
	rm -f src/*.o
	rm -f src/*.vfmanifest
	rm -f bin/libann_polarssl.so
	rm -f bin/libann_polarssl.dll.vfmanifest
	$(call pprint_big, Cleaned PolarSSL library)
