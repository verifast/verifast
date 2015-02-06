VF = ../../../../bin/verifast

include ../../Makefile.include

LIBS += -L ../bin -lann_polarssl
LIBS += -L ../polarssl_library/library -lpolarssl
LIBS += -pthreads -lpthread
LIBS += -lm

PROTOCOLS = \
	rpc \
	secure_storage \
	secure_communication_encryption \
	secure_communication_authenticated_encryption \

PROT_APPS = $(foreach prot,$(PROTOCOLS),$(prot)/$(prot))

all : $(PROT_APPS)

.SECONDEXPANSION:

MSG = Verified, compiled and executed protocol:

$(PROT_APPS) : ../annotated_api/polarssl.h \
	       $$(addsuffix .vfmanifest, $$@) $$(addsuffix .o, $$@) \
	       $$(dir $$@)main_app.vfmanifest $$(dir $$@)main_app.o
	@$(VF) -allow_assume pthread.o ../bin/libann_polarssl.dll.vfmanifest \
	                $(addsuffix .vfmanifest, $@) $(dir $@)main_app.vfmanifest
	@$(CC) $(CFLAGS) $(addsuffix .o, $@) $(dir $@)main_app.o -o $@ $(LIBS)
	@LD_LIBRARY_PATH=:../bin ; ./$@
	$(call pprint_big, $(MSG), \t\t$(patsubst %/,%,$(dir $@)) )

clean :
	@rm -f $(PROT_APPS)
	rm -f */*.o
	rm -f */*.vfmanifest
	$(call pprint_big, Cleaned PolarSSL example protocols)

