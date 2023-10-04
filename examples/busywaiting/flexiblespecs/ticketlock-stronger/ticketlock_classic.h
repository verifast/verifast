// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#ifndef TICKETLOCK_CLASSIC_H
#define TICKETLOCK_CLASSIC_H

#include "ticketlock.h" // Only needed for ticketlock_nb_level_dims, which should be hidden.

#include "busywaiting.h"

struct ticketlock_classic;
typedef struct ticketlock_classic *ticketlock_classic;

/*@

predicate ticketlock_classic(ticketlock_classic lock; level level, predicate() inv);

@*/

ticketlock_classic create_ticketlock_classic();
//@ requires exists<pair<level, predicate()> >(pair(?level, ?inv)) &*& func_lt_level(ticketlock_classic_acquire, level) == true &*& inv();
//@ ensures ticketlock_classic(result, level, inv);
//@ terminates;

/*@

predicate ticketlock_classic_held(ticketlock_classic lock, level level, predicate() inv, real frac, pair<void *, level> ob);

@*/

void ticketlock_classic_acquire(ticketlock_classic lock);
//@ requires obs(?p, ?obs) &*& [?f]ticketlock_classic(lock, ?level, ?inv) &*& forall(map(snd, obs), (level_lt)(level)) == true;
//@ ensures obs(?p1, cons(?ob, obs)) &*& is_ancestor_of(p, p1) == true &*& ticketlock_classic_held(lock, level, inv, f, ob) &*& inv() &*& level_of(ob) == level;
//@ terminates;

void ticketlock_classic_release(ticketlock_classic lock);
/*@
requires
    obs(?p, ?obs) &*& forall(map(snd, obs), (func_lt_level)(ticketlock_classic_acquire)) == true &*&
    ticketlock_classic_held(lock, ?level, ?inv, ?f, ?ob) &*& mem(ob, obs) == true &*& inv();
@*/
//@ ensures obs(?p1, remove(ob, obs)) &*& [f]ticketlock_classic(lock, level, inv) &*& is_ancestor_of(p, p1) == true;
//@ terminates;

void ticketlock_classic_dispose(ticketlock_classic lock);
//@ requires ticketlock_classic(lock, ?level, ?inv);
//@ ensures inv();
//@ terminates;

#endif
