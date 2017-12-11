# VERBOSE = -verbose -1
VF = ../../../bin/verifast -bindir ../bin/stdlib -vroot CRT=../bin/stdlib/ -I ../annotated_api

include ../Makefile.include

CFLAGS += -I include
CFLAGS += -I ../annotated_api/

MODULES = \
	general \
	debug \
	item \
	item_tags \
	well_formed \
	item_constraints \
	serialization \
	deserialization \
	invariants \
	key_register \
	data_item \
	pair_item \
	nonce_item \
	key_item \
	hash_item \
	hmac_item \
	symmetric_encrypted_item \
	asymmetric_encrypted_item \
	asymmetric_signature_item \
	asymmetric_authenticated_encryption \
	principal_ids \
	network \
	symbolic \
	attacker \

OBJECTS   = $(foreach module,$(MODULES),src/$(module).o)
MANIFESTS = $(foreach module,$(MODULES),src/$(module).vfmanifest)

OUT_LIB = libsymbolic.so

all: bin/symbolic.dll.vfmanifest $(OUT_LIB) example_protocols

include/switch_primitives.gh : tools/switch_primitives.py
	cd tools; \
	./switch_primitives.py; \
	mv switch_primitives.gh ../include

bin/symbolic.dll.vfmanifest : include/switch_primitives.gh $(MANIFESTS)
	mkdir -p bin
	@${VF} -shared -allow_assume -emit_dll_vfmanifest \
	         -emit_dll_vfmanifest_as bin/symbolic.dll.vfmanifest \
	         ../bin/libann_mbedTLS.dll.vfmanifest $(MANIFESTS)
	$(call pprint_big, Link time verification of crypto library done)

$(OUT_LIB) : include/switch_primitives.gh $(OBJECTS)
	mkdir -p bin
	@$(CC) -shared $(OBJECTS) -o bin/$(OUT_LIB)
	$(call pprint_big, Linked verified crypto library)

example_protocols : bin/symbolic.dll.vfmanifest $(OUT_LIB)
	make -C protocols

clean :
	rm -f bin/$(OUT_LIB)
	rm -f src/*.o
	rm -f src/*.vfmanifest
	rm -f bin/symbolic.dll.vfmanifest
	make -C protocols clean
	$(call pprint_big, Cleaned symbolic model library)



