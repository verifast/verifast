#ifndef CLHLOCK_H
#define CLHLOCK_H

struct lock;
struct lock_thread;

/*@

predicate lock(struct lock *lock; predicate() inv);
predicate lock_thread(struct lock_thread *thread);
predicate locked(struct lock_thread *thread, struct lock *lock, predicate() inv, real frac);

@*/

struct lock *create_lock();
    //@ requires exists<predicate()>(?inv) &*& inv();
    //@ ensures lock(result, inv);

struct lock_thread *create_lock_thread();
    //@ requires true;
    //@ ensures lock_thread(result);

void acquire(struct lock_thread *thread, struct lock *lock);
    //@ requires lock_thread(thread) &*& [?frac]lock(lock, ?inv);
    //@ ensures locked(thread, lock, inv, frac) &*& inv();

void release(struct lock_thread *thread);
    //@ requires locked(thread, ?lock, ?inv, ?frac) &*& inv();
    //@ ensures lock_thread(thread) &*& [frac]lock(lock, inv);

void dispose_lock_thread(struct lock_thread *thread);
    //@ requires lock_thread(thread);
    //@ ensures true;

void dispose_lock(struct lock *lock);
    //@ requires lock(lock, ?inv);
    //@ ensures inv();

#endif
