#include "stdlib.h"
#include "threading.h"

struct philosopher {
    struct lock *fork1;
    struct lock *fork2;
};

/*@

predicate_family_instance thread_run_data(philosopher_run)(struct philosopher *data) =
    data->fork1 |-> ?fork1 &*& [_]lock(fork1, ?fork1Id, _) &*&
    data->fork2 |-> ?fork2 &*& [_]lock(fork2, ?fork2Id, _) &*&
    malloc_block_philosopher(data) &*&
    lock_below(fork1Id, fork2Id) == true;

@*/

void create_philosopher(struct lock *fork1, struct lock *fork2)
    //@ requires [_]lock(fork1, ?fork1Id, _) &*& [_]lock(fork2, ?fork2Id, _) &*& lock_below(fork1Id, fork2Id) == true;
    //@ ensures true;
{
    struct philosopher *philosopher = malloc(sizeof(struct philosopher));
    if (philosopher == 0) abort();
    philosopher->fork1 = fork1;
    philosopher->fork2 = fork2;
    //@ close thread_run_data(philosopher_run)(philosopher);
    thread_start(philosopher_run, philosopher);
}

void philosopher_run(void *data) //@ : thread_run
    //@ requires thread_run_data(philosopher_run)(data) &*& lockset(currentThread, nil);
    //@ ensures false;
{
    //@ open thread_run_data(philosopher_run)(data);
    struct philosopher *philosopher = data;
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    while (true)
        //@ invariant [_]lock(fork1, ?fork1Id, _) &*& [_]lock(fork2, ?fork2Id, _) &*& lock_below(fork1Id, fork2Id) == true &*& lockset(currentThread, nil);
    {
        lock_acquire(fork2);
        lock_acquire(fork1);
        // Eat...
        lock_release(fork2); // Order does not matter. Non-nested order is supported.
        lock_release(fork1);
    }
}

//@ predicate dummy() = true;

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    //@ close dummy();
    //@ close create_lock_ghost_args(dummy, nil, nil);
    struct lock *forkA = create_lock();
    //@ assert lock(forkA, ?forkAId, _);
    //@ leak lock(forkA, forkAId, _);
    //@ close dummy();
    //@ close create_lock_ghost_args(dummy, cons(forkAId, nil), nil);
    struct lock *forkB = create_lock();
    //@ assert lock(forkB, ?forkBId, _);
    //@ leak lock(forkB, forkBId, _);
    //@ close dummy();
    //@ close create_lock_ghost_args(dummy, cons(forkAId, cons(forkBId, nil)), nil);
    struct lock *forkC = create_lock();
    //@ assert lock(forkC, ?forkCId, _);
    //@ leak lock(forkC, forkCId, _);
    create_philosopher(forkA, forkB);
    create_philosopher(forkB, forkC);
    create_philosopher(forkA, forkC);
    return 0;
}