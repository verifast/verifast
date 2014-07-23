#ifndef VF_MUTEX_H
#define VF_MUTEX_H

#include "include_ignored_by_verifast.h"
#include "vf_cleanup_debt.h"

/*
 * This API is the same as Verifast's thread.h mutex API, except that
 * create_mutex never fails while vf_mutex_create can fail (in that
 * case it returns 0).
 */


struct vf_mutex;


/*#
 * 
 * @param p: The predicate which can be acquired by opening the mutex.
 *           It might be useful to use a predicate constructor for the
 *           predicate p.
 */
/*@
predicate vf_mutex(struct vf_mutex *mutex ; predicate () p);
@*/


/*@
predicate vf_mutex_held(
	struct vf_mutex *mutex,
	predicate () p,
	int threadId,
	real frac);
@*/


/*#
 *
 * Used to pass the predicate p to the function vf_mutex_create.
 */
/*@
predicate vf_mutex_create_ghost_arg(predicate() p) = true;
@*/


/**
 * 
 * @return a mutex, 0 in case of failure.
 */
struct vf_mutex *vf_mutex_create();
/*@ requires
	vf_mutex_create_ghost_arg(?p)
	&*& p()
	&*& vf_cleanup_debt(?debtCount);
@*/
/*@ ensures
	result == 0 ? // failure
		p() &*& vf_cleanup_debt(debtCount)
	: // success
		vf_mutex(result, p) &*& vf_cleanup_debt(debtCount + 1);
@*/


void vf_mutex_dispose(struct vf_mutex *mutex);
//@ requires vf_mutex(mutex, ?p) &*& vf_cleanup_debt(?debtCount);
//@ ensures p() &*& vf_cleanup_debt(debtCount - 1);


/**
 * vf_mutex_lock - locks the mutex, you can now use the mutexed data
 * (or other resources).
 */
void vf_mutex_lock(struct vf_mutex *mutex);
//@ requires [?frac]vf_mutex(mutex, ?p);
//@ ensures p() &*& vf_mutex_held(mutex, p, currentThread, frac);


/**
 * vf_mutex_unlock - unlock the mutex, others can now use the mutexed data
 * (or other resources).
 */
void vf_mutex_unlock(struct vf_mutex *mutex);
//@ requires vf_mutex_held(mutex, ?p, currentThread, ?frac) &*& p();
//@ ensures [frac]vf_mutex(mutex, p);


#endif /* VF_MUTEX_H */
