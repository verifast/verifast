// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#ifndef SPINLOCK_H
#define SPINLOCK_H

#include "busywaiting.h"
#include "atomics.h"

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
    requires inv(?locked) &*& pre() &*& currentThread == callerThread &*& atomic_spaces(?spaces) &*& forall(spaces, (space_name_lt)(spinlock_acquire)) == true;
    ensures
        atomic_spaces(spaces) &*&
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
    requires inv(_) &*& pre() &*& atomic_spaces(?spaces) &*& forall(spaces, (space_name_lt)(spinlock_acquire)) == true;
    ensures inv(false) &*& post() &*& atomic_spaces(spaces);

@*/

void spinlock_release(spinlock_t spinlock);
//@ requires [?f]spinlock(spinlock, ?inv) &*& is_spinlock_release_ghost_op(?ghop, inv, ?pre, ?post) &*& pre();
//@ ensures [f]spinlock(spinlock, inv) &*& post();
//@ terminates;

void spinlock_dispose(spinlock_t spinlock);
//@ requires spinlock(spinlock, ?inv);
//@ ensures inv(_);
//@ terminates;

#endif
