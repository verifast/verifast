VF = ../../bin/verifast -bindir bin/stdlib

include Makefile.include

MODULES = \
  auxiliary_definitions \
  cs_to_ccs \
  cryptogram \
  cryptogram_levels \
  public_chars \
  interpret \
  havege_util \
  identifiers \
  attacker

OBJECTS   = $(foreach src,$(MODULES),src/$(addsuffix .o, $(src))) \
	    src/zeroize.o
MANIFESTS = $(foreach src,$(MODULES),src/$(addsuffix .vfmanifest, $(src)))

all: \
	polarssl_library \
	annotated_api/polarssl_definitions/macro_defines.h \
	stdlib \
	bin/libann_polarssl.dll.vfmanifest \
	bin/libann_polarssl.so \
	protocols \
	symbolic_model

polarssl_library :
	$(call pprint_big_begin, Downloading and compiling PolarSSL library)
	@wget https://tls.mbed.org/download/mbedtls-1.3.11-gpl.tgz; \
	 tar xvf mbedtls-1.3.11-gpl.tgz; \
	 mv mbedtls-1.3.11 polarssl_library; \
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
	make -C polarssl_library CC='$(CC)' -j4;
	$(call pprint_big_end)

.PHONY: annotated_api/polarssl_definitions/macro_defines.h
annotated_api/polarssl_definitions/macro_defines.h : polarssl_library tools/macro_defines.c
	@cd tools; \
	  ${CC} -I ../polarssl_library/include/polarssl/ macro_defines.c \
	    -lpthread -L ../polarssl_library/library -lpolarssl ; \
	  ./a.out; \
	  rm a.out; \
	  mv macro_defines.h ../annotated_api/polarssl_definitions;
	$(call pprint_big, Generated header with size and other defines for annotated PolarSSL library)

.PHONY: stdlib
stdlib:
	@test -d bin || mkdir bin; test -d bin/stdlib || mkdir bin/stdlib; \
	cp ../../bin/*.h bin/stdlib; \
	cp ../../bin/*.gh bin/stdlib; \
	cp ../../bin/*.c bin/stdlib; \
	cp ../../bin/*.vfmanifest bin/stdlib; \
	cp -r ../../bin/bits/ bin/stdlib
	@cd bin/stdlib/; chmod +x update_contracts.py; python ./update_contracts.py

bin/libann_polarssl.dll.vfmanifest : annotated_api/general_definitions/general_definitions.vfmanifest \
                                     annotated_api/polarssl_definitions/polarssl_definitions.vfmanifest \
                                     $(MANIFESTS)
	${VF} $(VFFLAGS) -shared -allow_assume \
	  -emit_dll_vfmanifest -emit_dll_vfmanifest_as \
	  bin/libann_polarssl.dll.vfmanifest \
	  annotated_api/general_definitions/general_definitions.vfmanifest \
	  annotated_api/polarssl_definitions/polarssl_definitions.vfmanifest \
	  $(MANIFESTS)
	$(call pprint_big, Link time verification of annotated PolarSSL library done)

bin/libann_polarssl.so : $(OBJECTS)
	@${CC} -shared $(OBJECTS) -o bin/libann_polarssl.so
	$(call pprint_big, Linked verified annotated PolarSSL library)

.PHONY: protocols
protocols:
	make -C protocols

.PHONY: symbolic_model
symbolic_model:
	make -C symbolic_model

clean:
	make -C symbolic_model clean
	make -C protocols clean
	rm -f src/*.o
	rm -f src/*.vfmanifest
	rm -f bin/libann_polarssl.so
	rm -f bin/libann_polarssl.dll.vfmanifest
	$(call pprint_big, Cleaned PolarSSL library)
