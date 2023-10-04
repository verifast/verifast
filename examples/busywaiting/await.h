#ifndef AWAIT_H
#define AWAIT_H

#include "mutex.h"

typedef bool condition
    /*@(
    level mutexLevel,
    list<pair<void *, level> > obs,
    predicate() inv,
    predicate(list<pathcomp> phase, void *) P,
    predicate(list<pathcomp> phase) Q,
    predicate(list<pathcomp> phase, void *data, void* signal, level level) R,
    list<pair<void *, level> > signals
    )@*/
    (void *data);
//@ requires obs(?phase0, cons(?ob, obs)) &*& inv() &*& P(phase0, data) &*& level_lt(mutexLevel, level_of(ob)) == true;
/*@
ensures
    obs(?phase1, cons(ob, obs)) &*& is_ancestor_of(phase0, phase1) == true &*&
    result ?
        signal(?s, ?level, false) &*& mem(pair(s, level), signals) == true &*&
        R(phase1, data, s, level) &*& forall(map(snd, obs), (level_lt)(level)) == true
    :
        inv() &*& Q(phase1);
@*/
//@ terminates;

/*@

typedef lemma void await_viewshift(predicate(list<pathcomp>, void *, void *, level) R, predicate() inv, void *data, predicate(list<pathcomp> phase, void *data) P)();
    requires signal(?signal, ?level, false) &*& R(?phase, data, signal, level);
    ensures inv() &*& P(phase, data);

@*/

void await(mutex mutex, condition *condition, void *data);
/*@
requires
    call_perm_(currentThread, condition) &*&
    obs(?phase0, ?obs) &*& [?f]mutex(mutex, ?level, ?inv) &*& [_]is_condition(condition, level, obs, inv, ?P, ?Q, ?R, ?signals) &*&
    call_below_perms(length(signals), phase0, ?caller) &*& func_lt(condition, caller) == true &*&
    P(phase0, data) &*& is_await_viewshift(?awaitViewshift, R, inv, data, P) &*& forall(map(snd, obs), (all_sublevels_lt)(mutex_nb_level_dims, level)) == true;
@*/
//@ ensures obs(?phase1, obs) &*& [f]mutex(mutex, level, inv) &*& Q(phase1) &*& is_await_viewshift(awaitViewshift, R, inv, data, P);

#endif
