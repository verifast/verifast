#ifndef SOCKETS_H
#define SOCKETS_H

#include "bool.h"
#include "malloc.h"
#include "stringBuffers.h"

struct server_socket;
struct socket;

/*@
predicate server_socket(struct server_socket *serverSocket);
predicate socket(struct socket *socket);
@*/

struct server_socket *create_server_socket(int port);
    //@ requires emp;
    //@ ensures server_socket(result);
struct socket *server_socket_accept(struct server_socket *serverSocket);
    //@ requires server_socket(serverSocket);
    //@ ensures server_socket(serverSocket) &*& socket(result);
void socket_write_string(struct socket* socket, char* string);
    //@ requires socket(socket) &*& [?f]chars(string, ?cs) &*& mem('\0', cs) == true;
    //@ ensures socket(socket) &*& [f]chars(string, cs);
void socket_write_string_buffer(struct socket *socket, struct string_buffer *buffer);
    //@ requires socket(socket) &*& [?f]string_buffer(buffer);
    //@ ensures socket(socket) &*& [f]string_buffer(buffer);
void socket_write_integer_as_decimal(struct socket *socket, int value);
    //@ requires socket(socket);
    //@ ensures socket(socket);
void socket_read_line(struct socket *socket, struct string_buffer *buffer);
    //@ requires socket(socket) &*& string_buffer(buffer);
    //@ ensures socket(socket) &*& string_buffer(buffer);
char* socket_read_line_as_string(struct socket* socket);
    //@ requires socket(socket);
    //@ ensures socket(socket) &*& result == 0 ? true : chars(result, ?cs) &*& mem('\0', cs) == true &*& malloc_block(result, length(cs));
int socket_read_nonnegative_integer(struct socket *socket);
    //@ requires socket(socket);
    //@ ensures socket(socket);

void socket_close(struct socket *socket);
    //@ requires socket(socket);
    //@ ensures emp;

#endif