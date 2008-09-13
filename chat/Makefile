CFLAGS=-g

chat.exe: stringBuffers.o lists.o socketlib.o sockets.o threading.o chat.o
	gcc -lpthread -o $@ $^

helloworld.exe: stringBuffers.c socketlib.c sockets.c helloworld.c
	gcc -o $@ $^