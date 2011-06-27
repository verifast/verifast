// An example where one thread repeatedly increments a shared counter,
// and another thread repeatedly observes it and asserts that the value increases.
// Demonstrates the use of ghost variables and fractional permissions to verify
// temporal properties in multithreaded programs. See also
// Bart Jacobs and Frank Piessens. Dynamic Owicki-Gries reasoning using ghost fields and fractional permissions. Technical Report CW-549, Department of Computer Science, Katholieke Universiteit Leuven, Belgium. June 2009.

#include "stdlib.h"
#include "threading.h"

struct counter {
    struct mutex *mutex;
    int count;
    //@ int oldCount;
};

/*@

predicate_ctor lock_invariant(struct counter *counter)() =
    counter->count |-> ?c &*& [1/2]counter->oldCount |-> ?oldCount &*& oldCount <= c;

predicate_family_instance thread_run_data(incrementor)(struct counter *counter) =
    counter->mutex |-> ?mutex &*& [1/2]mutex(mutex, lock_invariant(counter));

@*/

void incrementor(struct counter *counter) //@ : thread_run
    //@ requires thread_run_data(incrementor)(counter);
    //@ ensures true;
{
    //@ open thread_run_data(incrementor)(counter);
    struct mutex *mutex = counter->mutex;
    for (;;)
        //@ invariant [1/2]mutex(mutex, lock_invariant(counter));
    {
        mutex_acquire(mutex);
        //@ open lock_invariant(counter)();
        if (counter->count == INT_MAX) abort();
        counter->count++;
        //@ close lock_invariant(counter)();
        mutex_release(mutex);
    }
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct counter *counter = malloc(sizeof(struct counter));
    if (counter == 0) abort();
    counter->count = 0;
    //@ counter->oldCount = 0;
    //@ close lock_invariant(counter)();
    //@ close create_mutex_ghost_arg(lock_invariant(counter));
    struct mutex *mutex = create_mutex();
    counter->mutex = mutex;
    //@ close thread_run_data(incrementor)(counter);
    thread_start(incrementor, counter);
    
    int oldCount = 0;
    for (;;)
        //@ invariant [1/2]mutex(mutex, lock_invariant(counter)) &*& [1/2]counter->oldCount |-> oldCount;
    {
        mutex_acquire(mutex);
        //@ open lock_invariant(counter)();
        int count = counter->count;
        assert(count >= oldCount);
        oldCount = count;
        //@ counter->oldCount = count;
        //@ close lock_invariant(counter)();
        mutex_release(mutex);
    }
}