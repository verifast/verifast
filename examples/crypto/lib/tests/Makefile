#Compiler stuff
#--------------

CC = clang

CFLAGS += -I ../include

LIBS += -L .. -ldolevyao
LIBS += -L ../polarssl/library -lpolarssl
LIBS += -pthreads -lpthread 
LIBS += -lm

EXEC_NAME = tests
LIB_NAME  = dolevyao

#Test cases
#----------

OBJECTS = \
        items.o \
	nonce_items.o \
	key_items.o \
	data_items.o \
	hmac_items.o \
	encrypted_items.o \
	pair_items.o \
	networking.o

#Targets
#-------

all: run

$(EXEC_NAME): $(OBJECTS) ../lib$(LIB_NAME).a
	$(CC) $(CFLAGS) tests.c $(OBJECTS) $(LIBS) -o $(EXEC_NAME)

run: $(EXEC_NAME)
	./$(EXEC_NAME)

clean:
	rm -f *.o
	rm -f ${EXEC_NAME}

