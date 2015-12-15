#ifndef THREADING_H
#define THREADING_H

// The threading.c module provides two synchronization constructs: mutexes and
// locks. The only difference between these two constructs is that mutexes
// are non-re-entrant, whereas locks are re-entrant. Furthermore, the
// specifications for locks in this file prevent deadlock, whereas the
// specifications for mutexes do not. The benefit of using mutexes is
// that programs that use mutexes are easier to verify than programs that use
// locks.

// **** Mutexes ****

// Mutexes are non-re-entrant. Specifically, if a thread attempts to acquire a mutex that it already holds, the program aborts.

struct mutex;

/*@
predicate mutex(struct mutex *mutex; predicate() p);

predicate mutex_held(struct mutex *mutex, predicate() p, int threadId, real frac);

predicate create_mutex_ghost_arg(predicate() p) = true;

@*/


struct mutex *create_mutex();
    //@ requires create_mutex_ghost_arg(?p) &*& p();
    //@ ensures result != 0 &*& mutex(result, p);
    
void mutex_acquire(struct mutex *mutex);
    //@ requires [?f]mutex(mutex, ?p);
    //@ ensures mutex_held(mutex, p, currentThread, f) &*& p();

void mutex_release(struct mutex *mutex);
    //@ requires mutex_held(mutex, ?p, currentThread, ?f) &*& p();
    //@ ensures [f]mutex(mutex, p);

void mutex_dispose(struct mutex *mutex);
    //@ requires mutex(mutex, ?p);
    //@ ensures p();

// Condition variable, see e.g. pthread_cond_wait(3).
struct mutex_cond;
//@ predicate mutex_cond(struct mutex_cond *cond; struct mutex *mutex);

//@ predicate create_mutex_cond_ghost_args(struct mutex *mutex) = emp;
struct mutex_cond *create_mutex_cond();
    //@ requires create_mutex_cond_ghost_args(?mutex);
    //@ ensures result != 0 &*& mutex_cond(result, mutex);

void mutex_cond_dispose(struct mutex_cond *cond);
    //@ requires mutex_cond(cond, _);
    //@ ensures true;

void mutex_cond_wait(struct mutex_cond *cond, struct mutex *mutex);
    //@ requires [?fc]mutex_cond(cond, mutex) &*& mutex_held(mutex, ?p, currentThread, ?f) &*& p();
    //@ ensures [fc]mutex_cond(cond, mutex) &*& mutex_held(mutex, p, currentThread, f) &*& p();

void mutex_cond_signal(struct mutex_cond *cond);
    //@ requires [?fc]mutex_cond(cond, ?mutex) &*& mutex_held(mutex, ?p, currentThread, ?f);
    //@ ensures [fc]mutex_cond(cond, mutex) &*& mutex_held(mutex, p, currentThread, f);

// ghost critical sections
/*@
typedef lemma void mutex_ghost_critical_section_t
  (predicate() p, predicate() pre, predicate() post)
  ();
requires p() &*& pre();
ensures p() &*& post();

lemma void mutex_ghost_use(struct mutex *mutex, predicate() pre, predicate() post);
nonghost_callers_only
requires
  [?f]mutex(mutex, ?p)
  &*& pre()
  &*& is_mutex_ghost_critical_section_t(?critical_section, p, pre, post);
ensures
  [f]mutex(mutex, p)
  &*& post()
  &*& is_mutex_ghost_critical_section_t(critical_section, p, pre, post);
@*/

// **** Lock ordering for re-entry and deadlock prevention ****

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

// **** Standard locks (= POSIX mutexes/Win32 critical sections) ****

// The implementations are re-entrant; however, the contracts prevent re-entry since this would be unsound.
// (An alternative approach would be to allow re-entry, but not produce the invariant on re-entry.)
// The contracts enforce that a thread releases a lock only if it is currently holding the lock.

struct lock;

/*@

predicate lock(struct lock *lock; int lockId, predicate() p);

predicate locked(struct lock *lock, int lockId, predicate() p, int threadId, real frac);

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

// **** Threading ****

//@ predicate lockset(int threadId, list<int> lockIds);

// A distinction is made between non-joinable threads and joinable threads
// in the interest of leak checking.

// *** Non-joinable threads

//@ predicate_family thread_run_data(void *thread_run)(void *data);

typedef void thread_run(void *data);
    //@ requires thread_run_data(this)(data) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);

void thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_data(run)(data);
    //@ ensures true;

// *** Joinable threads

/*@

predicate_family thread_run_pre(void *thread_run)(void *data, any info);
predicate_family thread_run_post(void *thread_run)(void *data, any info);

@*/

typedef void thread_run_joinable(void *data);
    //@ requires thread_run_pre(this)(data, ?info) &*& lockset(currentThread, nil);
    //@ ensures thread_run_post(this)(data, info) &*& lockset(currentThread, nil);

struct thread;

/*@
predicate thread(struct thread *thread, void *thread_run, void *data, any info);
@*/

struct thread *thread_start_joinable(void *run, void *data);
    //@ requires is_thread_run_joinable(run) == true &*& thread_run_pre(run)(data, ?info);
    //@ ensures thread(result, run, data, info);

void thread_join(struct thread *thread);
    //@ requires thread(thread, ?run, ?data, ?info);
    //@ ensures thread_run_post(run)(data, info);

#endif