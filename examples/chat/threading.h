#ifndef THREADING_H
#define THREADING_H

struct lock;

/*@

predicate_family thread_run_data(void *run)(void *data);

predicate lock_invariant(predicate(void *) p, void *data);

lemma void open_lock_invariant(predicate(void *) p, void *data);
    requires lock_invariant(p, data);
    ensures p(data);

lemma void close_lock_invariant(predicate(void *) p, void *data);
    requires p(data);
    ensures lock_invariant(p, data);

predicate lock_permission(struct lock *lock, predicate(void *) p, void *data);

lemma void split_lock_permission(struct lock *lock);
    requires lock_permission(lock, ?p, ?data);
    ensures lock_permission(lock, p, data) &*& lock_permission(lock, p, data);

lemma void remove_lock_permission(struct lock *lock);
    requires lock_permission(lock, _, _);
    ensures emp;

@*/

typedef void (*thread_run)(void *data);
    //@ requires thread_run_data(this)(data);
    //@ ensures emp;

void thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_data(run)(data);
    //@ ensures emp;

struct lock *create_lock();
    //@ requires lock_invariant(?p, ?data);
    //@ ensures lock_permission(result, p, data);

void lock_acquire(struct lock *lock);   // TODO: Make the lock implementation non-reentrant; otherwise, this contract is unsound.
    //@ requires lock_permission(lock, ?p, ?data);
    //@ ensures lock_permission(lock, p, data) &*& lock_invariant(p, data);

void lock_release(struct lock *lock);
    //@ requires lock_permission(lock, ?p, ?data) &*& lock_invariant(p, data);
    //@ ensures lock_permission(lock, p, data);

#endif