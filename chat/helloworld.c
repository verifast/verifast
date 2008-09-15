struct server_socket;
struct socket;
struct writer;

/*@
predicate server_socket(struct server_socket *serverSocket);
predicate socket(struct socket *socket, struct writer *writer);
predicate socket_writer(struct writer *writer, struct socket *socket);
@*/

struct server_socket *create_server_socket(int port);
    //@ requires emp;
    //@ ensures server_socket(result);
struct socket *server_socket_accept(struct server_socket *serverSocket);
    //@ requires server_socket(serverSocket);
    //@ ensures server_socket(serverSocket) &*& socket(result, ?writer) &*& socket_writer(writer, result);

struct writer *socket_get_writer(struct socket *socket);
    //@ requires socket(socket, ?writer);
    //@ ensures socket(socket, writer) &*& result == writer;
void writer_write_string(struct writer *writer, char *string);
    //@ requires socket_writer(writer, ?socket);
    //@ ensures socket_writer(writer, socket);
void socket_close(struct socket *socket);
    //@ requires socket(socket, ?writer) &*& socket_writer(writer, socket);
    //@ ensures emp;

int main()
    //@ requires emp;
    //@ ensures emp;
{
    struct server_socket *serverSocket = create_server_socket(12345);

    while (1 == 1)
        //@ invariant server_socket(serverSocket);
    {
        struct socket *socket = server_socket_accept(serverSocket);
        void *blah = socket;
        struct socket *socket2 = blah;
        struct writer *writer = socket_get_writer(socket);
        writer_write_string(writer, "Hello, world!\r\n");
        socket_close(socket);
    }

    return 0;
}
