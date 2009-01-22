#ifndef THREADING_H
#define THREADING_H

struct lock;

/*@

predicate_family thread_run_data(void *run)(void *data);

predicate lock_invariant(predicate() p);

lemma void open_lock_invariant();
    requires lock_invariant(?p);
    ensures p();

lemma void close_lock_invariant(predicate() p);
    requires p();
    ensures lock_invariant(p);

predicate lock_permission(struct lock *lock, predicate() p);

lemma void split_lock_permission(struct lock *lock);
    requires lock_permission(lock, ?p);
    ensures lock_permission(lock, p) &*& lock_permission(lock, p);

lemma void remove_lock_permission(struct lock *lock);
    requires lock_permission(lock, _);
    ensures emp;

@*/

typedef void (*thread_run)(void *data);
    //@ requires thread_run_data(this)(data);
    //@ ensures emp;

void thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_data(run)(data);
    //@ ensures emp;

struct lock *create_lock();
    //@ requires lock_invariant(?p);
    //@ ensures lock_permission(result, p);

void lock_acquire(struct lock *lock);   // TODO: Make the lock implementation non-reentrant; otherwise, this contract is unsound.
    //@ requires lock_permission(lock, ?p);
    //@ ensures lock_permission(lock, p) &*& lock_invariant(p);

void lock_release(struct lock *lock);
    //@ requires lock_permission(lock, ?p) &*& lock_invariant(p);
    //@ ensures lock_permission(lock, p);

#endif