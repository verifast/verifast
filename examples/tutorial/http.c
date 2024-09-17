#include "stdlib.h"
#include "stringBuffers.h"
#include "sockets.h"
#include "threading.h"

static struct string_buffer *requests;
static struct mutex *requestsMutex;

/*@

predicate lock_invariant() =
    requests |-> ?requests_ &*& string_buffer(requests_, _);

predicate_family_instance
        thread_run_data(handle_connection)(struct socket *socket) =
    socket(socket, ?reader, ?writer) &*&
    reader(reader) &*& writer(writer) &*&
    [_]requestsMutex |-> ?mutex &*&
    [_]mutex(mutex, lock_invariant);

@*/

void handle_connection(struct socket *socket) //@ : thread_run
    //@ requires thread_run_data(handle_connection)(socket);
    //@ ensures true;
{
    //@ open thread_run_data(handle_connection)(socket);
    
    struct reader *reader = socket_get_reader(socket);
    struct writer *writer = socket_get_writer(socket);

    struct string_buffer *buffer = create_string_buffer();
    reader_read_line(reader, buffer);
    mutex_acquire(requestsMutex);
    //@ open lock_invariant();
    string_buffer_append_string_buffer(requests, buffer);
    string_buffer_append_string(requests, "\r\n");
    string_buffer_clear(buffer);
    string_buffer_append_string_buffer(buffer, requests);
    //@ close lock_invariant();
    mutex_release(requestsMutex);

    writer_write_string(writer,
        "HTTP/1.0 200 OK\r\n\r\n"
        "<html><head><title>Request Viewer</title></head>"
        "<body><p>Requests:</p><pre>\r\n");
    writer_write_string_buffer(writer, buffer);
    writer_write_string(writer, "</pre></body></html>\r\n");
    socket_close(socket);
    string_buffer_dispose(buffer);
}

int main() //@ : main_full(http)
    //@ requires module(http, true);
    //@ ensures true;
{
    //@ open_module();
    requests = create_string_buffer();
    //@ close lock_invariant();
    //@ close create_mutex_ghost_arg(lock_invariant);
    requestsMutex = create_mutex();
    //@ leak pointer(&requestsMutex, ?mutex) &*& mutex(mutex, _);
    
    struct server_socket *server = create_server_socket(80);
    for (;;)
       /*@
       invariant
           server_socket(server) &*&
           [_]pointer(&requestsMutex, mutex) &*&
           [_]mutex(mutex, lock_invariant);
       @*/
    {
        struct socket *socket = server_socket_accept(server);
        //@ close thread_run_data(handle_connection)(socket);
        thread_start(handle_connection, socket);
    }
}
