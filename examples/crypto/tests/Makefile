#Compiler stuff
#--------------

CC = clang

CFLAGS += -I ../include

LIBS += -L ../bin -lcryptolib
LIBS += -L ../polarssl/library -lpolarssl
LIBS += -pthreads -lpthread
LIBS += -lm

EXEC_NAME = tests
LIB_NAME  = cryptolib

#Test cases
#----------

OBJECTS = \
	nonce_items.o \
	key_items.o \
	data_items.o \
	hmac_items.o \
	pair_items.o \
	encrypted_items.o \
	networking.o

#Targets
#-------

all: run

$(EXEC_NAME): $(OBJECTS) ../bin/lib$(LIB_NAME).so
	$(CC) $(CFLAGS) tests.c $(OBJECTS) $(LIBS) -o $(EXEC_NAME)

run: $(EXEC_NAME)
	LD_LIBRARY_PATH=../bin/; ./$(EXEC_NAME)

clean:
	rm -f *.o
	rm -f ${EXEC_NAME}

