// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#ifndef TICKETLOCK_H
#define TICKETLOCK_H

#include "busywaiting.h"
#include "atomics.h"

struct ticketlock;
typedef struct ticketlock *ticketlock;

/*@

fixpoint int ticketlock_M_nb_dims() { return 1; } // TODO: Hide this from the client. (VeriFast does not yet support hiding fixpoint bodies.)

lemma_auto void ticketlock_M_nb_dims_nonneg();
    requires true;
    ensures 0 <= ticketlock_M_nb_dims;

predicate ticketlock(ticketlock lock; predicate(int, bool) inv);
predicate ticketlock_held(ticketlock lock, predicate(int, bool) inv, real f, int ticket);

@*/

ticketlock create_ticketlock();
//@ requires exists<predicate(int, bool)>(?inv) &*& inv(0, false);
//@ ensures ticketlock(result, inv);
//@ terminates;

/*@

typedef lemma void ticketlock_wait_ghost_op(predicate(int, bool) inv, predicate(int, list<int>, list<pathcomp>, list<pair<void *, level> >) wait_inv, int callerThread)(list<int> M);
    requires
        atomic_spaces(?spaces) &*& forall(map(fst, spaces), (func_gt)(ticketlock_dispose)) == true &*&
        obs(?p1, ?obs0) &*&
        inv(?owner, true) &*& length(M) == ticketlock_M_nb_dims &*&
        wait_inv(?owner0, ?M0, ?p0, obs0) &*& is_ancestor_of(p0, p1) == true &*& currentThread == callerThread &*&
        owner0 == -1 || owner == owner0 && M == M0 || lexprod_lt(M, M0) == true;
    ensures
        atomic_spaces(spaces) &*&
        obs(p1, ?obs1) &*& forall(map(snd, obs1), (func_lt_level)(ticketlock_acquire)) == true &*&
        inv(owner, true) &*& wait_inv(owner, M, p1, obs1) &*& call_perm_(currentThread, ticketlock_acquire);

typedef lemma void ticketlock_acquire_ghost_op(predicate(int, bool) inv, predicate(int, list<int>, list<pathcomp>, list<pair<void *, level> >) wait_inv, predicate(int) post, int callerThread)();
    requires
        atomic_spaces(?spaces) &*& forall(map(fst, spaces), (func_gt)(ticketlock_dispose)) == true &*&
        obs_(callerThread, ?p1, ?obs) &*&
        inv(?owner, false) &*& wait_inv(_, _, ?p0, obs) &*& is_ancestor_of(p0, p1) == true;
    ensures
        atomic_spaces(spaces) &*& inv(owner, true) &*& post(owner);

@*/

void ticketlock_acquire(ticketlock lock);
/*@
requires
    [?f]ticketlock(lock, ?inv) &*&
    obs(?p, ?obs) &*& forall(map(snd, obs), (func_lt_level)(ticketlock_acquire)) == true &*&
    is_ticketlock_wait_ghost_op(?wop, inv, ?wait_inv, currentThread) &*&
    is_ticketlock_acquire_ghost_op(?aop, inv, wait_inv, ?post, currentThread) &*&
    wait_inv(-1, _, p, obs);
@*/
//@ ensures ticketlock_held(lock, inv, f, ?ticket) &*& post(ticket);
//@ terminates;

/*@

typedef lemma void ticketlock_release_ghost_op(predicate(int, bool) inv, int ticket, list<pathcomp> p0, list<pair<void *, level> > obs, predicate() pre, predicate(list<pathcomp>, list<pair<void *, level> >) post, int callerThread)();
    requires
        atomic_spaces(?spaces) &*& forall(map(fst, spaces), (func_gt)(ticketlock_dispose)) == true &*&
        obs_(callerThread, ?p1, obs) &*& is_ancestor_of(p0, p1) == true &*&
        inv(ticket, true) &*& pre();
    ensures
        obs_(callerThread, p1, ?obs1) &*& forall(map(snd, obs1), (func_lt_level)(ticketlock_acquire)) == true &*&
        atomic_spaces(spaces) &*& inv(ticket + 1, false) &*& post(p1, obs1);

@*/

void ticketlock_release(ticketlock lock);
/*@
requires
    obs(?p, ?obs) &*& forall(map(snd, obs), (func_lt_level)(ticketlock_acquire)) == true &*&
    ticketlock_held(lock, ?inv, ?f, ?ticket) &*& is_ticketlock_release_ghost_op(?ghop, inv, ticket, p, obs, ?pre, ?post, currentThread) &*& pre();
@*/
//@ ensures obs(?p2, ?obs1) &*& post(?p1, obs1) &*& is_ancestor_of(p1, p2) == true &*& [f]ticketlock(lock, inv);
//@ terminates;

void ticketlock_dispose(ticketlock lock);
//@ requires ticketlock(lock, ?inv);
//@ ensures inv(_, false);
//@ terminates;

#endif
