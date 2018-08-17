#ifndef PTHREAD_H
#define PTHREAD_H

#include <threading.h>

#include <bits/pthreadtypes.h>


/*@

predicate pthread_thread(pthread_t thread, void *thread_run, void *data, any info);

predicate pthread_spinlock(pthread_spinlock_t *lock; int lockId, predicate() p);

predicate pthread_spinlock_locked(pthread_spinlock_t *lock, int lockId, predicate() p, int threadId, real frac);

predicate create_spinlock_ghost_args(predicate() p, list<int> lockLowerBounds, list<int> lockUpperBounds) = true;

fixpoint bool lock_below_top_x(int l, list<int> ls) {
    switch (ls) {
        case nil: return true;
        case cons(l0, ls0): return lock_below_top_x(l, ls0);
    }
}

predicate_family pthread_run_pre(void *pthread_run)(void *data, any info);
predicate_family pthread_run_post(void *pthread_run)(void *data, any info);

@*/

typedef void *pthread_run_joinable(void *data);
/*@ requires
        pthread_run_pre(this)(data, ?info)
    &*& lockset(currentThread, nil);
  @*/
/*@ ensures
        pthread_run_post(this)(data, info)
    &*& lockset(currentThread, nil)
    &*& result == 0;
  @*/

int pthread_spin_destroy(pthread_spinlock_t *lock);
/*@ requires
        pthread_spinlock(lock, ?lockId, ?p);
  @*/
/*@ ensures
        p()
    &*& integer(lock, _)
    &*& result == 0;
  @*/

int pthread_spin_init(pthread_spinlock_t *lock, int pshared);
/*@ requires
        create_lock_ghost_args(?p, ?ls, ?us) &*& p()
    &*& lock_all_below_all(ls, us) == true &*& integer(lock, _)
    &*& pshared == 0;
  @*/
/*@ ensures
        pthread_spinlock(lock, ?lockId, p)
    &*& lock_above_all(lockId, ls) == true
    &*& lock_below_all(lockId, us) == true
    &*& integer(lock, lockId)
    &*& result == 0;
  @*/

int pthread_spin_lock(pthread_spinlock_t *lock);
/*@ requires
        [?f]pthread_spinlock(lock, ?lockId, ?p)
    &*& lockset(currentThread, ?locks)
    &*& lock_below_top_x(lockId, locks) == true;
  @*/
/*@ ensures
        pthread_spinlock_locked(lock, lockId, p, currentThread, f)
    &*& p() &*& lockset(currentThread, cons(lockId, locks))
    &*& result == 0;
  @*/

int pthread_spin_unlock(pthread_spinlock_t *lock);
/*@ requires
        pthread_spinlock_locked(lock, ?lockId, ?p, currentThread, ?f)
    &*& p() &*& lockset(currentThread, ?locks);
  @*/
/*@ ensures
        [f]pthread_spinlock(lock, lockId, p)
    &*& lockset(currentThread, remove(lockId, locks))
    &*& result == 0;
  @*/

int pthread_join(pthread_t pthread, void **retval);
/*@ requires
        pthread_thread(pthread, ?run, ?data, ?info)
    &*& retval == (void *) 0;
  @*/
/*@ ensures
        pthread_run_post(run)(data, info)
    &*& result == 0;
  @*/

int pthread_create (pthread_t *pthread,
                    const pthread_attr_t *attr,
                    void *(*start_routine) (void *),
                    void *arg);
/*@ requires
        is_pthread_run_joinable(start_routine) == true
    &*& pthread_run_pre(start_routine)(arg, ?info)
    &*& u_integer(pthread, _)
    &*& attr == (void *) 0;
  @*/
/*@ ensures
        pthread_thread(?pthread_id, start_routine, arg, info)
    &*& u_integer(pthread, pthread_id)
    &*& result == 0;
  @*/


#endif
