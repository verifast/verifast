#ifndef THREADING_H
#define THREADING_H

struct lock;

/*@
predicate_family thread_run_pre(void *run)(void *data);

predicate_family thread_run_post(void *run)(void *data);

predicate create_lock_ghost_argument(predicate() p) = true;

predicate lock_permission(struct lock *lock; predicate() p);

predicate unlock_permission(struct lock *lock, predicate() p, real f);

predicate thread(struct thread *thread, void *thread_run, void *data);

@*/

struct thread;

typedef void thread_run(void *data);
    //@ requires thread_run_pre(this)(data);
    //@ ensures thread_run_post(this)(data);

struct thread* thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_pre(run)(data);
    //@ ensures thread(result, run, data);
    
void thread_join(struct thread *t);
    //@ requires thread(t, ?run, ?data);
    //@ ensures thread_run_post(run)(data);

struct lock *create_lock();
    //@ requires create_lock_ghost_argument(?p) &*& p();
    //@ ensures lock_permission(result, p);

void lock_acquire(struct lock *lock);  // Assumes that the lock is non-reentrant.
    //@ requires [?f]lock_permission(lock, ?p);
    //@ ensures unlock_permission(lock, p, f) &*& p();

void lock_release(struct lock *lock);
    //@ requires unlock_permission(lock, ?p, ?f) &*& p();
    //@ ensures [f]lock_permission(lock, p);
    
struct lock* lock_dispose(struct lock* l);
    //@ requires lock_permission(l, ?p);
    //@ ensures p();

#endif