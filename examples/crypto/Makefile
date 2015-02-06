VF = ../../bin/verifast

CFLAGS += -I include
CFLAGS += -I polarssl/polarssl_library/include/polarssl

include Makefile.include

MODULES = \
  general \
  debug \
  item \
  key_register \
  item_constraints \
  serialization \
  invariants \
  deserialization \
  data_item \
  pair_item \
  nonce_item \
  hash_item \
  key_item \
  hmac_item \
  symmetric_encrypted_item \
  asymmetric_encrypted_item \
  asymmetric_signature_item \
  asymmetric_authenticated_encryption \
  network \
  principals \
  cryptolib \
  attacker \

OBJECTS   = $(foreach module,$(MODULES),src/$(module).o)
MANIFESTS = $(foreach module,$(MODULES),src/$(module).vfmanifest)

OUT_LIB = libcryptolib.so

all: polar bin/cryptolib.dll.vfmanifest $(OUT_LIB) example_protocols

polar :
	make -C polarssl

bin/cryptolib.dll.vfmanifest : include/switch_primitives.gh $(MANIFESTS)
	mkdir -p bin
	@${VF} -shared -allow_assume -emit_dll_vfmanifest \
	         -emit_dll_vfmanifest_as bin/cryptolib.dll.vfmanifest \
	         polarssl/bin/libann_polarssl.so $(MANIFESTS)
	$(call pprint_big, Link time verification of crypto library done)

include/switch_primitives.gh : tools/switch_primitives.py
	cd tools; \
	./switch_primitives.py; \
	mv switch_primitives.gh ../include

$(OUT_LIB) : include/switch_primitives.gh $(OBJECTS)
	mkdir -p bin
	@$(CC) -shared $(OBJECTS) -o bin/$(OUT_LIB)
	$(call pprint_big, Linked verified crypto library)

example_protocols : bin/cryptolib.dll.vfmanifest $(OUT_LIB)
	make -C protocols

clean :
	$(call pprint_big_begin, Cleaning crypto library)
	rm -f bin/$(OUT_LIB)
	rm -f src/*.o
	rm -f src/*.vfmanifest
	rm -f bin/cryptolib.dll.vfmanifest
	make -C polarssl clean
	make -C protocols clean
	$(call pprint_big_end)

