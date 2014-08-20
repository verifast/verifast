#Compiler stuff
#--------------

CC = clang

CFLAGS += -D EXECUTE

LIBS += -L ../bin -lcryptolib
LIBS += -L ../polarssl/library -lpolarssl
LIBS += -pthreads -lpthread
LIBS += -lm

#Implemented Protocols
#---------------------

PROTOCOLS = \
	secure_storage \
	rpc \
	yahalom \
	nss \
	nsl

PROT_APPS = $(foreach prot,$(PROTOCOLS),$(prot)/$(prot))

#Targets
#-------

all : protocols_verify protocols_execute

protocols_compile : $(PROT_APPS)

protocols_execute : protocols_compile
	$(foreach exec,$(PROT_APPS), LD_LIBRARY_PATH=../bin/ ; ./$(exec) ;)

protocols_verify : 
	$(foreach prot,$(PROTOCOLS), cd $(prot); \
	      verifast -allow_assume ../../bin/libpolarssl.dll.vfmanifest \
	      ../../bin/cryptolib.dll.vfmanifest $(prot).c main_app.c; cd ..;) \

.SECONDEXPANSION:

$(PROT_APPS) : $$(addsuffix main_app.c, $$(dir $$@)) $$(addsuffix .c, $$@)
	$(CC) $(CFLAGS) $< $(addsuffix .c, $@) -o $@ $(LIBS);

clean :
	rm -f $(PROT_APPS)
