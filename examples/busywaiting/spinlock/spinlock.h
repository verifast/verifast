#ifndef SPINLOCK_H
#define SPINLOCK_H

#include "../busywaiting.h"

struct spinlock;
typedef struct spinlock *spinlock_t;

/*@

predicate spinlock(spinlock_t spinlock; predicate(bool) inv);

@*/

spinlock_t create_spinlock();
//@ requires exists<predicate(bool)>(?inv) &*& inv(false);
//@ ensures spinlock(result, inv);
//@ terminates;

/*@

typedef lemma void spinlock_acquire_ghost_op(predicate(bool) inv, predicate() pre, predicate() post, int callerThread)();
    requires inv(?locked) &*& pre() &*& currentThread == callerThread;
    ensures
        locked ?
            inv(locked) &*& pre() &*& call_perm_(currentThread, spinlock_acquire)
        :
            inv(true) &*& post();

@*/

void spinlock_acquire(spinlock_t spinlock);
//@ requires [?f]spinlock(spinlock, ?inv) &*& is_spinlock_acquire_ghost_op(?ghop, inv, ?pre, ?post, currentThread) &*& pre();
//@ ensures [f]spinlock(spinlock, inv) &*& post();
//@ terminates;

/*@

typedef lemma void spinlock_release_ghost_op(predicate(bool) inv, predicate() pre, predicate() post)();
    requires inv(_) &*& pre();
    ensures inv(false) &*& post();

@*/

void spinlock_release(spinlock_t spinlock);
//@ requires [?f]spinlock(spinlock, ?inv) &*& is_spinlock_release_ghost_op(?ghop, inv, ?pre, ?post) &*& pre();
//@ ensures [f]spinlock(spinlock, inv) &*& post();
//@ terminates;

#endif
