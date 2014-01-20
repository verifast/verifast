#Compiler stuff
#--------------

CC = clang

# DEBUG += -g -D DEBUG

CFLAGS += -I lib/include
CFLAGS += -I lib/polarssl/include 
CFLAGS += -D EXECUTE

LIBS += -L lib -ldolevyao 
LIBS += -L lib/polarssl/library -lpolarssl 
LIBS += -pthreads -lpthread 
LIBS += -lm

#Implemented Protocols
#---------------------

PROTOCOLS = \
	nsl \
	nss \
	yahalom \
	rpc \
	secure_storage \

PROT_APPS = $(foreach prot,$(PROTOCOLS),protocols/$(prot)/$(prot))

#Targets
#-------

all: protocols_execute

lib_:
	make -C lib
test_lib:
	make -C lib tests

protocols_verify: lib_
	../../bin/mysh -cpus $(NUMCPU) < crypto.mysh

protocols_compile: $(PROT_APPS)

protocols_execute: protocols_compile
	$(foreach exec,$(PROT_APPS), ./$(exec) ;)

.SECONDEXPANSION:

$(PROT_APPS): $$(addsuffix main.c, $$(dir $$@)) $$(addsuffix .c, $$@) lib_
	$(CC) $(DEBUG) $(CFLAGS) $< $(addsuffix .c, $@) -o $@ $(LIBS)
		

clean:
	make -C lib clean
	rm -f $(PROT_APPS)
