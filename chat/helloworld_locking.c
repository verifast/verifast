// By Bart Jacobs and Jan Smans

#include "malloc.h"
#include "bool.h"
#include "stringBuffers.h"
#include "sockets.h"
#include "threading.h"

struct counter {
    int count;
};

struct session {
    struct socket *socket;
    struct counter *counter;
    struct lock *counterLock;
};

/*@

predicate counter(struct counter *counter)
    requires counter->count |-> _;

predicate_family_instance lock_invariant(counterLabel)(void *data)
    requires counter(data);

predicate session(struct session *session)
    requires session->socket |-> ?socket &*& socket(socket, ?writer) &*& socket_writer(writer, socket)
      &*& session->counter |-> ?counter &*& session->counterLock |-> ?lock &*& lock_permission(lock, counterLabel, counter)
      &*& malloc_block_session(session);

predicate_family_instance thread_run_data(session_run)(void *data)
    requires session(data);

@*/

void counterLabel() // Used only as a label.
    //@ requires emp;
    //@ ensures emp;
{
}

void session_run(void *data) /*@ : thread_run @*/
{
    //@ open thread_run_data(session_run)(data);
    struct session *session = data;
    //@ open session(session);
    struct socket *socket = session->socket;
    struct counter *counter = session->counter;
    struct lock *lock = session->counterLock;
    free(session);
    
    lock_acquire(lock);
    //@ open lock_invariant(counterLabel)(counter);
    //@ open counter(counter);
    {
        int count = counter->count;
        counter->count = count + 1;
    }
    //@ close counter(counter);
    //@ close lock_invariant(counterLabel)(counter);
    lock_release(lock);
    //@ remove_lock_permission(lock);
    
    {
        struct writer *writer = socket_get_writer(socket);
        writer_write_string(writer, "Hello, world!\r\n");
        socket_close(socket);
    }
}

int main()
    //@ requires emp;
    //@ ensures emp;
{
    struct counter *counter = malloc(sizeof(struct counter));
    counter->count = 0;
    //@ close counter(counter);
    //@ close lock_invariant(counterLabel)(counter);
    {
        struct lock *lock = create_lock();
        
        struct server_socket *serverSocket = create_server_socket(12345);

        while (true)
            //@ invariant server_socket(serverSocket) &*& lock_permission(lock, counterLabel, counter);
        {
            struct socket *socket = server_socket_accept(serverSocket);
            //@ split_lock_permission(lock);
            struct session *session = malloc(sizeof(struct session));
            session->socket = socket;
            session->counter = counter;
            session->counterLock = lock;
            //@ close session(session);
            //@ close thread_run_data(session_run)(session);
            thread_start(session_run, session);
        }

        return 0;
    }
}
