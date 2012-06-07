#ifndef THREADING_H
#define THREADING_H

// Lock ordering for re-entry and deadlock prevention.
// Note: we use lock IDs instead of struct lock pointers because
// 1) if a lock is disposed and its address is reused for a new lock, it could be inserted in a different place in the lock order DAG,
// causing inconsistency, and
// 2) this enables including other lock implementations into the lock order as well.

/*@

fixpoint bool lock_below(int l1, int l2);

lemma void lock_below_trans(int l1, int l2, int l3);
    requires lock_below(l1, l2) == true &*& lock_below(l2, l3) == true;
    ensures lock_below(l1, l3) == true;

lemma void lock_below_antirefl(int l1, int l2);
    requires lock_below(l1, l2) == true;
    ensures l1 != l2;

fixpoint bool lock_below_all(int l, list<int> ls) {
    switch (ls) {
        case nil: return true;
        case cons(l0, ls0): return lock_below(l, l0) && lock_below_all(l, ls0);
    }
}

fixpoint bool lock_all_below_all(list<int> ls, list<int> us) {
    switch (ls) {
        case nil: return true;
        case cons(l, ls0): return lock_below_all(l, us) && lock_all_below_all(ls0, us);
    }
}

fixpoint bool lock_above_all(int l, list<int> ls) {
    switch (ls) {
        case nil: return true;
        case cons(l0, ls0): return lock_below(l0, l) && lock_above_all(l, ls0);
    }
}

fixpoint bool lock_below_top(int l, list<int> ls) {
    switch (ls) {
        case nil: return true;
        case cons(l0, ls0): return lock_below(l, l0);
    }
}

@*/

// Standard locks (= POSIX mutexes/Win32 critical sections)
// The implementations are re-entrant; however, the contracts prevent re-entry since this would be unsound.
// (An alternative approach would be to allow re-entry, but not produce the invariant on re-entry.)
// The contracts enforce that a thread releases a lock only if it is currently holding the lock.

struct lock;

/*@

predicate lock(struct lock *lock; int lockId, predicate() p);

predicate locked(struct lock *lock, int lockId, predicate() p, int threadId, real frac);

predicate lockset(int threadId, list<int> locks);

predicate create_lock_ghost_args(predicate() p, list<int> lockLowerBounds, list<int> lockUpperBounds) = true;

@*/

struct lock *create_lock();
    //@ requires create_lock_ghost_args(?p, ?ls, ?us) &*& p() &*& lock_all_below_all(ls, us) == true;
    //@ ensures lock(result, ?lockId, p) &*& lock_above_all(lockId, ls) == true &*& lock_below_all(lockId, us) == true;

void lock_acquire(struct lock *lock);
    //@ requires [?f]lock(lock, ?lockId, ?p) &*& lockset(currentThread, ?locks) &*& lock_below_top(lockId, locks) == true;
    //@ ensures locked(lock, lockId, p, currentThread, f) &*& p() &*& lockset(currentThread, cons(lockId, locks));

void lock_release(struct lock *lock);
    //@ requires locked(lock, ?lockId, ?p, currentThread, ?f) &*& p() &*& lockset(currentThread, ?locks);
    //@ ensures [f]lock(lock, lockId, p) &*& lockset(currentThread, remove(lockId, locks));

void lock_dispose(struct lock *lock);
    //@ requires lock(lock, ?lockId, ?p);
    //@ ensures p();

/*@

predicate_family thread_run_data(void *run)(void *data);

@*/

typedef void thread_run(void *data);
    //@ requires thread_run_data(this)(data) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);

void thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_data(run)(data);
    //@ ensures emp;

#endif