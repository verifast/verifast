VF = ../../../bin/verifast

include ../Makefile.include

LIBS += -L ../bin -lcryptolib
LIBS += -L ../polarssl/bin/ -lann_polarssl
LIBS += -L ../polarssl/polarssl_library/library/ -lpolarssl
LIBS += -pthreads -lpthread
LIBS += -lm

LD_PATH = ../bin/:../polarssl/bin:../polarssl/polarssl_library/library

PROTOCOLS = \
	dummy_protocol \
	secure_storage \
	rpc \
	yahalom \
	secure_storage_asym \
	nsl \

PROT_APPS = $(foreach prot,$(PROTOCOLS),$(prot)/$(prot))

all : $(PROT_APPS)

.SECONDEXPANSION:

MSG = Verified, compiled and executed protocol:

$(PROT_APPS) : $$(addsuffix .vfmanifest, $$@) $$(addsuffix .o, $$@) \
	       $$(dir $$@)main_app.vfmanifest $$(dir $$@)main_app.o
	@$(VF) -allow_assume pthread.o \
           ../polarssl/bin/libann_polarssl.dll.vfmanifest \
           ../bin/cryptolib.dll.vfmanifest \
	   $(addsuffix .vfmanifest, $@) $(dir $@)main_app.vfmanifest
	@$(CC) $(CFLAGS) $(addsuffix .o, $@) $(dir $@)main_app.o -o $@ $(LIBS)
	@LD_LIBRARY_PATH=$(LD_PATH) ; ./$@
	$(call pprint_big, $(MSG), \t\t$(patsubst %/,%,$(dir $@)) )

clean :
	rm -f */*.o
	rm -f */*.vfmanifest
	@rm -f $(PROT_APPS)
	$(call pprint_big, Cleaned crypto example protocols)
