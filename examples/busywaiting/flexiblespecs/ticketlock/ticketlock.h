// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#ifndef TICKETLOCK_H
#define TICKETLOCK_H

#include "busywaiting.h"

struct ticketlock;
typedef struct ticketlock *ticketlock;

/*@

fixpoint int ticketlock_nb_level_dims() { return 1; } // TODO: Hide this from the client. (VeriFast does not yet support hiding fixpoint bodies.)

lemma_auto void ticketlock_nb_level_dims_nonneg();
    requires true;
    ensures 0 <= ticketlock_nb_level_dims();

predicate ticketlock(ticketlock lock; level level, predicate(int, bool) inv);
predicate ticketlock_held(ticketlock lock, level level, predicate(int, bool) inv, real f, int ticket);

@*/

ticketlock create_ticketlock();
/*@
requires
    exists<pair<level, predicate(int, bool)> >(pair(?level, ?inv)) &*& inv(0, false) &*&
    ticketlock_nb_level_dims <= level_subspace_nb_dims(level);
@*/
//@ ensures ticketlock(result, level, inv);
//@ terminates;

/*@

typedef lemma void ticketlock_wait_ghost_op(level level, predicate(int, bool) inv, predicate(int, void *, list<pathcomp>) wait_inv, int callerThread)(void *f);
    requires
        obs(?p1, ?obs) &*& forall(map(snd, obs), (level_lt)(level)) == true &*&
        inv(?owner, true) &*& 0 <= owner &*&
        wait_inv(?owner0, ?f0, ?p0) &*& is_ancestor_of(p0, p1) == true &*& currentThread == callerThread &*& func_lt(f, ticketlock_acquire) == true &*&
        owner == owner0 ? f == f0 : owner0 < owner &*& call_below_perm(p1, ticketlock_acquire);
    ensures
        obs(p1, obs) &*& inv(owner, true) &*& wait_inv(owner, f, p1) &*& call_perm_(currentThread, f);

typedef lemma void ticketlock_acquire_ghost_op(list<pair<void *, level> > obs, level level, predicate(int, bool) inv, predicate(int, void *, list<pathcomp>) wait_inv, predicate(int) post, int callerThread)();
    requires
        obs_(callerThread, ?p1, obs) &*&
        inv(?owner, false) &*& wait_inv(_, _, ?p0) &*& is_ancestor_of(p0, p1) == true;
    ensures inv(owner, true) &*& post(owner);

@*/

void ticketlock_acquire(ticketlock lock);
/*@
requires
    [?f]ticketlock(lock, ?level, ?inv) &*&
    obs(?p, ?obs) &*& 
    forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, level)) == true &*&
    is_ticketlock_wait_ghost_op(?wop, level, inv, ?wait_inv, currentThread) &*&
    is_ticketlock_acquire_ghost_op(?aop, obs, level, inv, wait_inv, ?post, currentThread) &*&
    wait_inv(-1, _, p);
@*/
//@ ensures ticketlock_held(lock, level, inv, f, ?ticket) &*& post(ticket);
//@ terminates;

/*@

typedef lemma void ticketlock_release_ghost_op(predicate(int, bool) inv, int ticket, predicate() pre, predicate() post)();
    requires inv(ticket, true) &*& pre();
    ensures inv(ticket + 1, false) &*& post();

@*/

void ticketlock_release(ticketlock lock);
//@ requires ticketlock_held(lock, ?level, ?inv, ?f, ?ticket) &*& is_ticketlock_release_ghost_op(?ghop, inv, ticket, ?pre, ?post) &*& pre();
//@ ensures [f]ticketlock(lock, level, inv) &*& post();
//@ terminates;

void ticketlock_dispose(ticketlock lock);
//@ requires ticketlock(lock, ?level, ?inv);
//@ ensures inv(_, false);
//@ terminates;

#endif
