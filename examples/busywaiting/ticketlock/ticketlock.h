#ifndef TICKETLOCK_H
#define TICKETLOCK_H

#include "../busywaiting.h"

struct ticketlock;
typedef struct ticketlock *ticketlock;

/*@

fixpoint int ticketlock_nb_level_dims() { return 1; } // TODO: Hide this from the client. (VeriFast does not yet support hiding fixpoint bodies.)

lemma_auto void ticketlock_nb_level_dims_nonneg();
    requires true;
    ensures 0 <= ticketlock_nb_level_dims();

predicate ticketlock(ticketlock lock; list<int> level, predicate(int, bool) inv);

@*/

ticketlock create_ticketlock();
/*@
requires
    exists<pair<list<int>, predicate(int, bool)> >(pair(?level, ?inv)) &*& inv(0, false) &*&
    level == cons(?level_max_length, ?level0) &*& length(level0) + ticketlock_nb_level_dims <= level_max_length;
@*/
//@ ensures ticketlock(result, level, inv);
//@ terminates;

/*@

typedef lemma void ticketlock_wait_ghost_op(list<pathcomp> p, list<int> level, predicate(int, bool) inv, predicate(int, void *) wait_inv, int callerThread)(void *f);
    requires
        obs(?p1, ?obs) &*& is_ancestor_of(p, p1) == true &*& forall(map(snd, obs), (level_lt)(level)) == true &*&
        inv(?owner, true) &*& 0 <= owner &*& wait_inv(?owner0, ?f0) &*& currentThread == callerThread &*& func_lt(f, ticketlock_acquire) == true &*&
        owner == owner0 ? f == f0 : owner0 < owner &*& call_below_perm_(currentThread, ticketlock_acquire);
    ensures
        obs(p1, obs) &*& inv(owner, true) &*& wait_inv(owner, f) &*& call_perm_(currentThread, f);

typedef lemma void ticketlock_acquire_ghost_op(list<pathcomp> p, list<int> level, predicate(int, bool) inv, predicate(int, void *) wait_inv, predicate() post, int callerThread)();
    requires
        obs(?p1, ?obs) &*& is_ancestor_of(p, p1) == true &*& forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, level)) == true &*&
        inv(?owner, false) &*& wait_inv(_, _) &*& currentThread == callerThread;
    ensures inv(owner, true) &*& post();

@*/

void ticketlock_acquire(ticketlock lock);
/*@
requires
    [?f]ticketlock(lock, ?level, ?inv) &*&
    obs(?p, ?obs) &*& 
    forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, level)) == true &*&
    is_ticketlock_wait_ghost_op(?wop, p, level, inv, ?wait_inv, currentThread) &*&
    is_ticketlock_acquire_ghost_op(?aop, p, level, inv, wait_inv, ?post, currentThread) &*&
    wait_inv(-1, _);
@*/
//@ ensures [f]ticketlock(lock, level, inv) &*& post();
//@ terminates;

/*@

typedef lemma void ticketlock_release_ghost_op(predicate(int, bool) inv, predicate() pre, predicate() post, int callerThread)();
    requires inv(?owner, true) &*& pre() &*& currentThread == callerThread;
    ensures inv(owner + 1, false) &*& post();

@*/

void ticketlock_release(ticketlock lock);
//@ requires [?f]ticketlock(lock, ?level, ?inv) &*& is_ticketlock_release_ghost_op(?ghop, inv, ?pre, ?post, currentThread) &*& pre();
//@ ensures [f]ticketlock(lock, level, inv) &*& post();
//@ terminates;

#endif
