// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#ifndef TICKETLOCK_STRONG
#define TICKETLOCK_STRONG

#include "atomics.h"

struct ticketlock_strong;
typedef struct ticketlock_strong *ticketlock_strong;

//@ predicate ticketlock_strong(ticketlock_strong lock; predicate(int, bool) inv);
//@ predicate ticketlock_strong_locked(ticketlock_strong lock, predicate(int, bool) inv, real frac, int owner);

ticketlock_strong create_ticketlock_strong();
//@ requires exists<predicate(int, bool)>(?inv) &*& inv(0, false);
//@ ensures ticketlock_strong(result, inv);
//@ terminates;

/*@

typedef lemma void ticketlock_strong_wait_ghost_op(predicate(int, bool) inv, predicate(int, int) waitInv, int acquireThread)(int M);
    requires
        atomic_spaces(?spaces) &*& forall(map(fst, spaces), (func_gt)(ticketlock_strong_dispose)) == true &*&
        inv(?owner, true) &*& 0 <= owner &*&
        waitInv(?oldOwner, ?oldM) &*& 0 <= M &*& oldOwner == -1 || owner == oldOwner && M == oldM || oldOwner < owner && M < oldM &*& currentThread == acquireThread;
    ensures
        atomic_spaces(spaces) &*& 
        inv(owner, true) &*& waitInv(owner, M) &*& call_perm_(currentThread, ticketlock_strong_acquire);

typedef lemma void ticketlock_strong_acquire_ghost_op(predicate(int, bool) inv, predicate(int, int) waitInv, predicate(int) post)();
    requires
        atomic_spaces(?spaces) &*& forall(map(fst, spaces), (func_gt)(ticketlock_strong_dispose)) == true &*&
        inv(?owner, false) &*& waitInv(_, _);
    ensures
        atomic_spaces(spaces) &*& 
        inv(owner, true) &*& post(owner);

@*/

void ticketlock_strong_acquire(ticketlock_strong lock);
/*@
requires
    [?f]ticketlock_strong(lock, ?inv) &*&
    is_ticketlock_strong_wait_ghost_op(?waitOp, inv, ?waitInv, currentThread) &*&
    is_ticketlock_strong_acquire_ghost_op(?acqOp, inv, waitInv, ?post) &*&
    waitInv(-1, _);
@*/
//@ ensures ticketlock_strong_locked(lock, inv, f, ?owner) &*& post(owner);
//@ terminates;

/*@

typedef lemma void ticketlock_strong_release_ghost_op(predicate(int, bool) inv, int owner, predicate() pre, predicate() post)();
    requires
        atomic_spaces(?spaces) &*& forall(map(fst, spaces), (func_gt)(ticketlock_strong_dispose)) == true &*&
        inv(owner, true) &*& pre();
    ensures
        atomic_spaces(spaces) &*& 
        inv(owner + 1, false) &*& post();

@*/

void ticketlock_strong_release(ticketlock_strong lock);
//@ requires ticketlock_strong_locked(lock, ?inv, ?f, ?owner) &*& is_ticketlock_strong_release_ghost_op(?relOp, inv, owner, ?pre, ?post) &*& pre();
//@ ensures [f]ticketlock_strong(lock, inv) &*& post();
//@ terminates;

void ticketlock_strong_dispose(ticketlock_strong lock);
//@ requires ticketlock_strong(lock, ?inv);
//@ ensures inv(_, false);
//@ terminates;

#endif
