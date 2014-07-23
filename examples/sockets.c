#include <stdlib.h> /* abort */
#include <string.h> /* memset */
#include <stdio.h> /* printf, perror */
#include <sys/types.h>

#ifdef WIN32

//#include <winsock.h> /* send, recv */
#include <winsock2.h>
#include <process.h> /* _exit */
typedef int ssize_t;

#else

#include <sys/socket.h>   /* socket(), bind(), listen(), accept() */
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h> /* fork, write, close */
#define SOCKET int
#define INVALID_SOCKET (-1)

#endif

#include <stdbool.h>
#include "stringBuffers.h"
#include "sockets.h"

void print_socket_error_message(char *api)
{
#ifdef WIN32
    printf("Socket API call '%s' failed: error code %d\n", api, WSAGetLastError());
#else
    perror(api);
#endif
}

SOCKET socket_create_and_listen(int port)
{
    SOCKET serverSocket = 0;
    struct sockaddr_in serverName = { 0 };
    int status = 0;

#ifdef WIN32
    {
        WSADATA windowsSocketsApiData;
        WSAStartup(MAKEWORD(2, 0), &windowsSocketsApiData);
    }
#endif

    serverSocket = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (INVALID_SOCKET == serverSocket)
    {
        print_socket_error_message("socket()");
        abort();
    }
    
    serverName.sin_addr.s_addr=htonl(INADDR_ANY);
    serverName.sin_family = AF_INET;
    /* network-order */
    serverName.sin_port = htons(port);

    status = bind(serverSocket, (struct sockaddr *) &serverName, sizeof(serverName));
    if (INVALID_SOCKET == status)
    {
        print_socket_error_message("bind()");
        abort();
    }
    
    status = listen(serverSocket, 5);  // Allow 5 pending incoming connection requests
    if (INVALID_SOCKET == status)
    {
        print_socket_error_message("listen()");
        abort();
    }

    return serverSocket;
}

SOCKET socket_accept(SOCKET serverSocket)
{
    struct sockaddr_in clientName = { 0 };
    SOCKET slaveSocket;
    int clientLength = sizeof(clientName);

    (void) memset(&clientName, 0, sizeof(clientName));

    slaveSocket = accept(serverSocket, (struct sockaddr *) &clientName, &clientLength);
    if (INVALID_SOCKET == slaveSocket)
    {
        print_socket_error_message("accept()");
        abort();
    }
    
    return slaveSocket;
}

SOCKET socket_create(int port)
{
    SOCKET lsocket;
    SOCKADDR_IN lSockAddr;
    SOCKET serverSocket = 0;
    int status = 0;

#ifdef WIN32
    {
        WSADATA windowsSocketsApiData;
        WSAStartup(MAKEWORD(2, 0), &windowsSocketsApiData);
    }
#endif

    lsocket = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (INVALID_SOCKET == lsocket)
    {
        print_socket_error_message("socket()");
        abort();
    }

    memset(&lSockAddr,0, sizeof(lSockAddr));
    lSockAddr.sin_family = AF_INET;
    lSockAddr.sin_port = htons(port);
    lSockAddr.sin_addr.s_addr = inet_addr("127.0.0.1");
    status = connect(lsocket,(SOCKADDR *)&lSockAddr,sizeof(SOCKADDR_IN));
    if(status != 0)
    {
        print_socket_error_message("connect()");
        abort();
    }
    return lsocket;
}

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
    string_buffer_clear(buffer);
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
            {
                ssize_t count = recv(reader->handle, reader->buffer, READER_BUFFER_SIZE, 0);
                if (count < 0) {
                    print_socket_error_message("recv()");
                    abort();
                }
                if (count == 0)
                    return true;
                reader->bufferEnd = reader->buffer + count;
            }
        }
    }
}

struct writer {
    int handle;
};

void writer_write_string(struct writer *writer, char *text)
{
    size_t length = strlen(text);
    send(writer->handle, text, length, 0);
}

void writer_write_string_buffer(struct writer *writer, struct string_buffer *buffer)
{
    send(writer->handle, string_buffer_get_chars(buffer), string_buffer_get_length(buffer), 0);
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
    struct writer *writer = malloc(sizeof(struct writer));
    struct socket *socket = malloc(sizeof(struct socket));
    reader->handle = handle;
    reader->bufferStart = reader->buffer;
    reader->bufferEnd = reader->buffer;
    writer->handle = handle;
    socket->handle = handle;
    socket->reader = reader;
    socket->writer = writer;
    return socket;
}

struct socket *create_client_socket(int port)
{
    int handle = socket_create(port);
    struct reader *reader = malloc(sizeof(struct reader));
    struct writer *writer = malloc(sizeof(struct writer));
    struct socket *socket = malloc(sizeof(struct socket));
    reader->handle = handle;
    writer->handle = handle;
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
    return socket->writer;
}

void socket_close(struct socket *socket)
{
#ifdef WIN32
    closesocket(socket->handle);
#else
    close(socket->handle);
#endif
    free(socket->reader);
    free(socket->writer);
    free(socket);
}
