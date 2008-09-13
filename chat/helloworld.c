struct server_socket;

struct server_socket *create_server_socket(int port);
struct socket *server_socket_accept(struct server_socket *serverSocket);

struct writer;

struct writer *socket_get_writer(struct socket *socket);
void writer_write_string(struct writer *writer, char *string);
void socket_close(struct socket *socket);

int main()
    //@ requires emp;
    //@ ensures emp;
{
    struct server_socket *serverSocket = create_server_socket(12345);

    while (1 == 1)
    {
        struct socket *socket = server_socket_accept(serverSocket);
        struct writer *writer = socket_get_writer(socket);
        writer_write_string(writer, "Hello, world!\r\n");
        socket_close(socket);
    }

    return 0;
}
