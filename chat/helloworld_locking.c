// By Bart Jacobs and Jan Smans

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

/* threading.h */

typedef void (*thread_run)(void *data);
    //@ requires thread_run_data(this)(data);
    //@ ensures emp;

/*@
predicate_family thread_run_data(thread_run run)(void *data);
@*/

void thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_data(run)(data);
    //@ ensures emp;

struct lock;

/*@
predicate_family lock_invariant(void *label)(void *data);
predicate lock_permission(struct lock *lock, void *label, void *data);

lemma void split_lock_permission(struct lock *lock);
    requires lock_permission(lock, ?label, ?data);
    ensures lock_permission(lock, label, data) &*& lock_permission(lock, label, data); // TODO: Disable the ambiguous match check.
lemma void remove_lock_permission(struct lock *lock);
    requires lock_permission(lock, _, _);
    ensures emp;
@*/

struct lock *create_lock();
    //@ requires lock_invariant(?label)(?data);
    //@ ensures lock_permission(result, label, data);

void lock_acquire(struct lock *lock);   // TODO: Make the lock implementation non-reentrant; otherwise, this contract is unsound.
    //@ requires lock_permission(lock, ?label, ?data);
    //@ ensures lock_permission(lock, label, data) &*& lock_invariant(label)(data);

void lock_release(struct lock *lock);
    //@ requires lock_permission(lock, ?label, ?data) &*& lock_invariant(label)(data);
    //@ ensures lock_permission(lock, label, data);

/* client code */

struct counter {
    int count;
};

struct session {
    struct socket *socket;
    struct counter *counter;
    struct lock *counterLock;
};

void counterLabel() // Used only as a label.
    //@ requires emp;
    //@ ensures emp;
{
}

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

        while (1 == 1)
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
