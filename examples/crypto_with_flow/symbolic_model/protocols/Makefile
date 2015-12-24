VF = ../../../../bin/verifast -bindir ../../bin/stdlib/

include ../../Makefile.include

LIBS += -L ../bin -lsymbolic
LIBS += -L ../../bin/ -lann_polarssl
LIBS += -L ../../polarssl_library/library/ -lpolarssl
LIBS += -pthreads -lpthread
LIBS += -lm

LD_PATH = ../bin/:../../bin:../../polarssl_library/library

PROTOCOLS = \
	dummy_protocol \
	secure_storage \
	secure_storage_asym \
	rpc \
	recursive_otway_rees \

PROT_APPS = $(foreach prot,$(PROTOCOLS),$(prot)/$(prot))

all : $(PROT_APPS)

.SECONDEXPANSION:

MSG = Verified, compiled and executed protocol:

$(PROT_APPS) : $$(addsuffix .vfmanifest, $$@) $$(addsuffix .o, $$@) \
	       $$(dir $$@)main_app.vfmanifest $$(dir $$@)main_app.o
	@$(VF) -allow_assume pthread.o \
	  ../../bin/libann_polarssl.dll.vfmanifest \
	  ../bin/symbolic.dll.vfmanifest \
	   $(addsuffix .vfmanifest, $@) $(dir $@)main_app.vfmanifest
	@$(CC) $(CFLAGS) $(addsuffix .o, $@) $(dir $@)main_app.o -o $@ $(LIBS)
	@LD_LIBRARY_PATH=$(LD_PATH) ; ./$@
	$(call pprint_big, $(MSG), \t\t$(patsubst %/,%,$(dir $@)) )

clean :
	rm -f */*.o
	rm -f */*.vfmanifest
	@rm -f $(PROT_APPS)
	$(call pprint_big, Cleaned symbolic model protocols)
