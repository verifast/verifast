struct lock;

/*@

predicate_family thread_run_data(void *run)(void *data);

predicate_family lock_invariant(void *label)(void *data);

predicate lock_permission(struct lock *lock, void *label, void *data);

lemma void split_lock_permission(struct lock *lock);
    requires lock_permission(lock, ?label, ?data);
    ensures lock_permission(lock, label, data) &*& lock_permission(lock, label, data);

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
    //@ requires lock_invariant(?label)(?data);
    //@ ensures lock_permission(result, label, data);

void lock_acquire(struct lock *lock);   // TODO: Make the lock implementation non-reentrant; otherwise, this contract is unsound.
    //@ requires lock_permission(lock, ?label, ?data);
    //@ ensures lock_permission(lock, label, data) &*& lock_invariant(label)(data);

void lock_release(struct lock *lock);
    //@ requires lock_permission(lock, ?label, ?data) &*& lock_invariant(label)(data);
    //@ ensures lock_permission(lock, label, data);
