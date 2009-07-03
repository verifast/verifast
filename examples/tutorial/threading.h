#ifndef THREADING_H
#define THREADING_H

struct lock;

/*@
predicate_family thread_run_data(void *run)(void *data);

predicate_family thread_run_post(void *run)(void *data);

predicate lock_invariant(predicate() p);

lemma void open_lock_invariant();
    requires lock_invariant(?p);
    ensures p();

lemma void close_lock_invariant(predicate() p);
    requires p();
    ensures lock_invariant(p);

predicate lock_permission(struct lock *lock, predicate() p);

predicate unlock_permission(struct lock *lock, predicate() p, real f);

lemma void split_lock_permission(struct lock *lock);
    requires [?f]lock_permission(lock, ?p);
    ensures [f/2]lock_permission(lock, p) &*& [f/2]lock_permission(lock, p);
    
lemma void merge_lock_permission(struct lock *lock);
    requires [?f]lock_permission(lock, ?p) &*& [?g]lock_permission(lock, p);
    ensures [f + g]lock_permission(lock, p);
    
   
predicate thread(struct thread *thread, void *thread_run, void *data);

@*/

struct thread;

typedef void thread_run(void *data);
    //@ requires thread_run_data(this)(data);
    //@ ensures thread_run_post(this)(data);

struct thread* thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_data(run)(data);
    //@ ensures thread(result, run, data);
    
void thread_join(struct thread *t);
    //@ requires thread(t, ?run, ?data);
    //@ ensures thread_run_post(run)(data);

struct lock *create_lock();
    //@ requires lock_invariant(?p);
    //@ ensures lock_permission(result, p);

void lock_acquire(struct lock *lock);   // TODO: Make the lock implementation non-reentrant; otherwise, this contract is unsound.
    //@ requires [?f]lock_permission(lock, ?p);
    //@ ensures unlock_permission(lock, p, f) &*& lock_invariant(p);

void lock_release(struct lock *lock);
    //@ requires unlock_permission(lock, ?p, ?f) &*& lock_invariant(p);
    //@ ensures [f]lock_permission(lock, p);
    
struct lock* lock_dispose(struct lock* l);
    //@ requires lock_permission(l, ?p);
    //@ ensures lock_invariant(p);
    

#endif