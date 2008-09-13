#include <malloc.h>
#include <string.h>
#include <unistd.h>
#include <stdio.h> /* For perror */
#include "socketlib.h"

#include "bool.h"
#include "stringBuffers.h"
#include "sockets.h"

struct server_socket {
    int handle;
};

struct server_socket *create_server_socket(int port)
{
    int handle = socket_create_and_listen(port);
    struct server_socket *serverSocket = malloc(sizeof(struct server_socket));
    serverSocket->handle = handle;
    return serverSocket;
}

#define READER_BUFFER_SIZE 4096

struct reader {
    int handle;
    char *bufferStart;
    char *bufferEnd;
    char buffer[READER_BUFFER_SIZE];
};

bool reader_read_line(struct reader *reader, struct string_buffer *buffer)
{
    for (;;)
    {
        void *newline = memchr(reader->bufferStart, '\n', reader->bufferEnd - reader->bufferStart);
        if (newline != 0) {
            char *end = (char *)newline;
            if (reader->bufferStart < end && *(end - 1) == '\r')
                end--;
            string_buffer_append_chars(buffer, reader->bufferStart, end - reader->bufferStart);
            reader->bufferStart = (char *)newline + 1;
            return false;
        } else {
            string_buffer_append_chars(buffer, reader->bufferStart, reader->bufferEnd - reader->bufferStart);
            reader->bufferStart = reader->buffer;
            ssize_t count = read(reader->handle, reader->buffer, READER_BUFFER_SIZE);
            if (count < 0) {
                perror("read()");
                _exit(1);
            }
            if (count == 0)
                return true;
            reader->bufferEnd = reader->buffer + count;
        }
    }
}

struct writer {
    int handle;
};

void writer_write_string(struct writer *writer, char *text)
{
    int length = strlen(text);
    write(writer->handle, text, length);
}

void writer_write_string_buffer(struct writer *writer, struct string_buffer *buffer)
{
    write(writer->handle, string_buffer_get_chars(buffer), string_buffer_get_length(buffer));
}

struct socket {
    int handle;
    struct reader *reader;
    struct writer *writer;
};

struct socket *server_socket_accept(struct server_socket *serverSocket)
{
    int handle = socket_accept(serverSocket->handle);
    struct reader *reader = malloc(sizeof(struct reader));
    reader->handle = handle;
    struct writer *writer = malloc(sizeof(struct writer));
    writer->handle = handle;
    struct socket *socket = malloc(sizeof(struct socket));
    socket->handle = handle;
    socket->reader = reader;
    socket->writer = writer;
    return socket;
}

struct reader *socket_get_reader(struct socket *socket)
{
    return socket->reader;
}

struct writer *socket_get_writer(struct socket *socket)
{
    return  socket->writer;
}

void socket_close(struct socket *socket)
{
    close(socket->handle);
    free(socket->reader);
    free(socket->writer);
    free(socket);
}
