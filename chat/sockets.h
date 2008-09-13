struct writer;

void writer_write_string(struct writer *writer, char *text);
void writer_write_string_buffer(struct writer *writer, struct string_buffer *buffer);

struct reader;

bool reader_read_line(struct reader *reader, struct string_buffer *buffer);

struct server_socket;
struct socket;

struct server_socket *create_server_socket(int port);
struct socket *server_socket_accept(struct server_socket *serverSocket);
struct reader *socket_get_reader(struct socket *socket);
struct writer *socket_get_writer(struct socket *socket);
void socket_close(struct socket *socket);
