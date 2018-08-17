VF = ../../bin/verifast -bindir bin/stdlib

include Makefile.include

MODULES = \
  auxiliary_definitions \
  ccs \
  cryptogram \
  cryptogram_levels \
  public_chars \
  interpret \
  identifiers \
  memcmp \

PMODULES = \
  havege_util \
  attacker

OBJECTS   = $(foreach src,$(MODULES),bin/stdlib/crypto/$(addsuffix .o, $(src))) \
	    bin/stdlib/crypto/zeroize.o
MANIFESTS = $(foreach src,$(MODULES),bin/stdlib/crypto/$(addsuffix .vfmanifest, $(src)))

POBJECTS   = $(foreach src,$(PMODULES),annotated_api/$(addsuffix .o, $(src)))
PMANIFESTS = $(foreach src,$(PMODULES),annotated_api/$(addsuffix .vfmanifest, $(src)))

all: \
	mbedTLS_library \
	annotated_api/macro_defines.h \
	stdlib \
	bin/libann_mbedTLS.dll.vfmanifest \
	bin/libann_mbedTLS.so \
	protocols \
	symbolic_model

mbedTLS_library :
	$(call pprint_big_begin, Downloading and compiling mbed TLS library)
	@wget https://tls.mbed.org/download/mbedtls-1.3.11-gpl.tgz; \
	 tar xvf mbedtls-1.3.11-gpl.tgz; \
	 mv mbedtls-1.3.11 mbedTLS_library; \
	 cd mbedTLS_library; \
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
	make -C mbedTLS_library CC='$(CC)' -j4;
	$(call pprint_big_end)

.PHONY: annotated_api/macro_defines.h
annotated_api/macro_defines.h : mbedTLS_library tools/macro_defines.c
	@cd tools; \
	  ${CC} -I ../mbedTLS_library/include/polarssl/ macro_defines.c \
	    -lpthread -L ../mbedTLS_library/library -lpolarssl ; \
	  ./a.out; \
	  rm a.out; \
	  mv macro_defines.h ../annotated_api;
	$(call pprint_big, Generated header with size and other defines for annotated mbed TLS library)

.PHONY: stdlib
stdlib:
	@test -d bin || mkdir bin; test -d bin/stdlib || mkdir bin/stdlib; \
	cp ../../bin/*.h bin/stdlib; \
	cp ../../bin/*.gh bin/stdlib; \
	cp ../../bin/*.c bin/stdlib; \
	cp ../../bin/*.vfmanifest bin/stdlib; \
	cp -r ../../bin/bits/ bin/stdlib
	@cd bin/stdlib/; chmod +x update_contracts.py; python ./update_contracts.py

bin/libann_mbedTLS.dll.vfmanifest : bin/stdlib/crypto.vfmanifest \
                                     annotated_api/mbedTLS_definitions.vfmanifest \
                                     $(MANIFESTS) $(PMANIFESTS)
	${VF} $(VFFLAGS) -shared -allow_assume \
	  -emit_dll_vfmanifest -emit_dll_vfmanifest_as \
	  bin/libann_mbedTLS.dll.vfmanifest \
	  bin/stdlib/crypto.vfmanifest \
	  annotated_api/mbedTLS_definitions.vfmanifest \
	  $(MANIFESTS) $(PMANIFESTS)
	$(call pprint_big, Link time verification of annotated mbed TLS library done)

bin/libann_mbedTLS.so : $(OBJECTS) $(POBJECTS)
	@${CC} -shared $(OBJECTS) $(POBJECTS) -o bin/libann_mbedTLS.so
	$(call pprint_big, Linked verified annotated mbed TLS library)

.PHONY: protocols
protocols:
	make -C protocols

.PHONY: symbolic_model
symbolic_model:
	make -C symbolic_model

clean:
	make -C symbolic_model clean
	make -C protocols clean
	rm -f $(OBJECTS) $(POBJECTS) $(MANIFESTS) $(PMANIFESTS)
	rm -f bin/libann_mbedTLS.so
	rm -f bin/libann_mbedTLS.dll.vfmanifest
	$(call pprint_big, Cleaned mbed TLS library)
