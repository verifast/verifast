#ifndef THREADING_H
#define THREADING_H

struct lock;

/*@

predicate_family thread_run_data(void *run)(void *data);

predicate lock(struct lock *lock; predicate() p);

predicate locked(struct lock *lock, predicate() p, int threadId, real frac);

predicate create_lock_ghost_arg(predicate() p) = true;

@*/

typedef void thread_run(void *data);
    //@ requires thread_run_data(this)(data);
    //@ ensures emp;

void thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_data(run)(data);
    //@ ensures emp;

struct lock *create_lock();
    //@ requires create_lock_ghost_arg(?p) &*& p();
    //@ ensures lock(result, p);

void lock_acquire(struct lock *lock); // Assumes that locks are non-reentrant.
    //@ requires [?f]lock(lock, ?p);
    //@ ensures locked(lock, p, currentThread, f) &*& p();

void lock_release(struct lock *lock);
    //@ requires locked(lock, ?p, currentThread, ?f) &*& p();
    //@ ensures [f]lock(lock, p);

#endif