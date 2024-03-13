#include <stdlib.h>
#include <threading.h>

struct MutexCell<T> {
  mutex mutex;
  T payload;
};

/*@

predicate_ctor MutexCell_inv<T>(struct MutexCell<T> *mutexCell, predicate(T) T_own)() =
    mutexCell->payload |-> ?payload &*& T_own(payload);

predicate MutexCell<T>(struct MutexCell<T> *mutexCell, predicate(T) T_own;) =
    malloc_block_MutexCell<T>(mutexCell) &*&
    mutexCell->mutex |-> ?mutex &*&
    mutex(mutex, (MutexCell_inv)(mutexCell, T_own));

predicate MutexCell_held<T>(struct MutexCell<T> *mutexCell, predicate(T) T_own, int thread_id, real q) =
    [q]malloc_block_MutexCell<T>(mutexCell) &*&
    [q]mutexCell->mutex |-> ?mutex &*&
    mutex_held(mutex, MutexCell_inv<T>(mutexCell, T_own), thread_id, q);

@*/

struct MutexCell<T> *create_MutexCell<T>(T value)
//@ requires exists<predicate(T)>(?T_own) &*& (T_own)(value);
//@ ensures MutexCell<T>(result, T_own);
{
    //@ open exists(_);
    struct MutexCell<T> *result = malloc(sizeof(struct MutexCell<T>));
    if (result == 0) abort();
    result->payload = value;
    //@ close MutexCell_inv<T>(result, T_own)();
    //@ close create_mutex_ghost_arg(MutexCell_inv<T>(result, T_own));
    mutex mutex = create_mutex();
    result->mutex = mutex;
    return result;
}

void MutexCell_acquire<T>(struct MutexCell<T> *mutexCell)
//@ requires [?q]MutexCell<T>(mutexCell, ?T_own);
//@ ensures MutexCell_held<T>(mutexCell, T_own, currentThread, q) &*& mutexCell->payload |-> ?payload &*& T_own(payload);
{
    mutex_acquire(mutexCell->mutex);
    //@ open MutexCell_inv<T>(mutexCell, T_own)();
    //@ close MutexCell_held<T>(mutexCell, T_own, currentThread, q);
}

void MutexCell_release<T>(struct MutexCell<T> *mutexCell)
//@ requires MutexCell_held<T>(mutexCell, ?T_own, currentThread, ?q) &*& mutexCell->payload |-> ?payload &*& T_own(payload);
//@ ensures [q]MutexCell<T>(mutexCell, T_own);
{
    //@ open MutexCell_held<T>(mutexCell, T_own, currentThread, q);
    //@ close MutexCell_inv<T>(mutexCell, T_own)();
    mutex_release(mutexCell->mutex);
}
