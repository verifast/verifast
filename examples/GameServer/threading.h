#ifndef THREADING_H
#define THREADING_H

//@ #include "list.h"

// Standard locks (= POSIX mutexes/Win32 critical sections)
// The implementations are re-entrant; however, the contracts prevent re-entry since this would be unsound.
// (An alternative approach would be to allow re-entry, but not produce the invariant on re-entry.)
// The contracts enforce that a thread releases a lock only if it is currently holding the lock.

struct lock;

/*@

predicate lock(struct lock *lock; predicate() p);

predicate locked(struct lock *lock, predicate() p, int threadId, real frac);

predicate lockset(int threadId, list<int> locks);

predicate create_lock_ghost_args(predicate() p) = true;

@*/

struct lock *create_lock();
    //@ requires create_lock_ghost_args(?p) &*& p() ;
    //@ ensures lock(result, p);

void lock_acquire(struct lock *lock);
    //@ requires [?f]lock(lock, ?p);
    //@ ensures locked(lock, p, currentThread, f) &*& p();

void lock_release(struct lock *lock);
    //@ requires locked(lock, ?p, currentThread, ?f) &*& p();
    //@ ensures [f]lock(lock, p);

void lock_dispose(struct lock *lock);
    //@ requires lock(lock, ?p);
    //@ ensures p();

/*@

predicate_family thread_run_pre(void *thread_run)(void *data);
predicate_family thread_run_post(void *thread_run)(void *data);

@*/

typedef void thread_run(void *data);
    //@ requires thread_run_pre(this)(data) &*& lockset(currentThread, nil);
    //@ ensures thread_run_post(this)(data) &*& lockset(currentThread, nil);

struct thread;

/*@
predicate thread(struct thread *thread, void *thread_run, void *data);
@*/

struct thread *thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_pre(run)(data);
    //@ ensures thread(result, run, data);
    
void thread_join(struct thread *thread);
    //@ requires thread(thread, ?run, ?data);
    //@ ensures thread_run_post(run)(data);

#endif