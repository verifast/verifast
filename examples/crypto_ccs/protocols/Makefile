# VERBOSE = -verbose -1
VF = ../../../bin/verifast -bindir ../bin/stdlib -vroot CRT=../bin/stdlib/

include ../Makefile.include

LIBS += -L ../bin -lann_polarssl
LIBS += -L ../polarssl_library/library -lpolarssl
LIBS += -pthreads -lpthread
LIBS += -lm

PROTOCOLS = \
	dummy \
	hmac \
	rpc \
	enc_then_hmac \
	enc_and_hmac \
	hmac_then_enc \
	hmac_then_enc_tagged \
	hmac_then_enc_nested \
	auth_enc \
	sign \
	nsl \
	yahalom \


PROT_APPS = $(foreach prot,$(PROTOCOLS),$(prot)/$(prot))

all : $(PROT_APPS)

.SECONDEXPANSION:

MSG = Verified, compiled and executed protocol:

$(PROT_APPS) : ../annotated_api/polarssl_definitions/polarssl_definitions.h \
	       $$(addsuffix .vfmanifest, $$@) $$(addsuffix .o, $$@) \
	       $$(dir $$@)main_app.vfmanifest $$(dir $$@)main_app.o
	$(VF) $(VFFLAGS) -allow_assume pthread.o ../bin/libann_polarssl.dll.vfmanifest \
	                $(addsuffix .vfmanifest, $@) $(dir $@)main_app.vfmanifest
	$(CC) $(CFLAGS) $(addsuffix .o, $@) $(dir $@)main_app.o -o $@ $(LIBS)
	@LD_LIBRARY_PATH=:../bin ; ./$@
	$(call pprint_big, $(MSG), \t\t$(patsubst %/,%,$(dir $@)) )

stats :
	$(foreach prot, $(PROTOCOLS), \
	  echo "\n\n$(prot)\n\n"; \
	  cd $(prot); \
	  cloc .; \
	  time -v ../../../../bin/verifast -bindir ../../bin/stdlib -vroot CRT=../../bin/stdlib/ \
	                -allow_assume pthread.o  ../../bin/libann_polarssl.dll.vfmanifest \
	                $(addsuffix .c, $(prot)) main_app.vfmanifest; \
	  cd ..; \
	)

clean :
	@rm -f $(PROT_APPS)
	rm -f */*.o
	rm -f */*.vfmanifest
	$(call pprint_big, Cleaned PolarSSL example protocols)

