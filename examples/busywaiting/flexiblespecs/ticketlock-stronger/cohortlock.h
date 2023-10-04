// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#ifndef COHORTLOCK_H
#define COHORTLOCK_H

#include "busywaiting.h"
#include "atomics.h"

struct cohortlock;
typedef struct cohortlock *cohortlock;
struct cohort;
typedef struct cohort *cohort;

/*@

fixpoint int cohortlock_M_nb_dims() { return 5; } // TODO: Hide this from the client. (VeriFast does not yet support hiding fixpoint bodies.)

lemma_auto void cohortlock_M_nb_dims_nonneg();
    requires true;
    ensures 0 <= cohortlock_M_nb_dims;

predicate cohortlock(cohortlock lock; predicate(int, bool) inv);
predicate cohort(cohort cohort; cohortlock lock, predicate(int, bool) inv, real frac);
predicate cohortlock_held(cohort cohort, cohortlock lock, predicate(int, bool) inv, real fc, real f, int ticket);

@*/

cohortlock create_cohortlock();
//@ requires exists<predicate(int, bool)>(?inv) &*& inv(0, false);
//@ ensures cohortlock(result, inv);
//@ terminates;

cohort create_cohort(cohortlock lock);
//@ requires [?f]cohortlock(lock, ?inv);
//@ ensures cohort(result, lock, inv, f);
//@ terminates;

/*@

typedef lemma void cohortlock_wait_ghost_op(predicate(int, bool) inv, predicate(int, list<int>, list<pathcomp>, list<pair<void *, level> >) wait_inv, int callerThread)(list<int> M);
    requires
        atomic_spaces(?spaces) &*& forall(map(fst, spaces), (func_gt)(cohortlock_dispose)) == true &*&
        obs(?p1, ?obs0) &*&
        inv(?owner, true) &*& length(M) == cohortlock_M_nb_dims &*&
        wait_inv(?owner0, ?M0, ?p0, obs0) &*& is_ancestor_of(p0, p1) == true &*& currentThread == callerThread &*&
        owner0 == -1 || owner == owner0 && M == M0 || lexprod_lt(M, M0) == true;
    ensures
        atomic_spaces(spaces) &*&
        obs(p1, ?obs1) &*& forall(map(snd, obs1), (func_lt_level)(cohortlock_acquire)) == true &*&
        inv(owner, true) &*& wait_inv(owner, M, p1, obs1) &*& call_perm_(currentThread, cohortlock_acquire);

typedef lemma void cohortlock_acquire_ghost_op(predicate(int, bool) inv, predicate(int, list<int>, list<pathcomp>, list<pair<void *, level> >) wait_inv, predicate(int) post, int callerThread)();
    requires
        atomic_spaces(?spaces) &*& forall(map(fst, spaces), (func_gt)(cohortlock_dispose)) == true &*&
        obs_(callerThread, ?p1, ?obs) &*&
        inv(?owner, false) &*& wait_inv(_, _, ?p0, obs) &*& is_ancestor_of(p0, p1) == true;
    ensures atomic_spaces(spaces) &*& inv(owner, true) &*& post(owner);

@*/

void cohortlock_acquire(cohort cohort);
/*@
requires
    [?f]cohort(cohort, ?lock, ?inv, ?fc) &*&
    obs(?p, ?obs) &*& forall(map(snd, obs), (func_lt_level)(cohortlock_acquire)) == true &*&
    is_cohortlock_wait_ghost_op(?wop, inv, ?wait_inv, currentThread) &*&
    is_cohortlock_acquire_ghost_op(?aop, inv, wait_inv, ?post, currentThread) &*&
    wait_inv(-1, _, p, obs);
@*/
//@ ensures cohortlock_held(cohort, lock, inv, fc, f, ?ticket) &*& post(ticket);
//@ terminates;

/*@

typedef lemma void cohortlock_release_ghost_op(predicate(int, bool) inv, int ticket, list<pathcomp> p0, list<pair<void *, level> > obs, predicate() pre, predicate(list<pathcomp>, list<pair<void *, level> >) post, int callerThread)();
    requires
        atomic_spaces(?spaces) &*& forall(map(fst, spaces), (func_gt)(cohortlock_dispose)) == true &*&
        obs_(callerThread, ?p1, obs) &*& is_ancestor_of(p0, p1) == true &*&
        inv(ticket, true) &*& pre();
    ensures
        obs_(callerThread, p1, ?obs1) &*& forall(map(snd, obs1), (func_lt_level)(cohortlock_acquire)) == true &*&
        atomic_spaces(spaces) &*& inv(ticket + 1, false) &*& post(p1, obs1);

@*/

void cohortlock_release(cohort cohort);
/*@
requires
    obs(?p, ?obs) &*& forall(map(snd, obs), (func_lt_level)(cohortlock_acquire)) == true &*&
    cohortlock_held(cohort, ?lock, ?inv, ?fc, ?f, ?ticket) &*& is_cohortlock_release_ghost_op(?ghop, inv, ticket, p, obs, ?pre, ?post, currentThread) &*& pre();
@*/
//@ ensures obs(?p2, ?obs1) &*& post(?p1, obs1) &*& is_ancestor_of(p1, p2) == true &*& [f]cohort(cohort, lock, inv, fc);
//@ terminates;

void cohort_dispose(cohort cohort);
//@ requires cohort(cohort, ?lock, ?inv, ?f);
//@ ensures [f]cohortlock(lock, inv);
//@ terminates;

void cohortlock_dispose(cohortlock lock);
//@ requires cohortlock(lock, ?inv);
//@ ensures inv(_, false);
//@ terminates;

#endif
