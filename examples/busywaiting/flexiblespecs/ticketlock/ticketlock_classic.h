// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#ifndef TICKETLOCK_CLASSIC_H
#define TICKETLOCK_CLASSIC_H

#include "ticketlock.h" // Only needed for ticketlock_nb_level_dims, which should be hidden.

#include "busywaiting.h"

struct ticketlock_classic;
typedef struct ticketlock_classic *ticketlock_classic;

/*@

fixpoint int ticketlock_classic_nb_level_dims() { return 1 + ticketlock_nb_level_dims; } // TODO: Hide this fixpoint body from clients.

predicate ticketlock_classic(ticketlock_classic lock; level level, predicate() inv);

@*/

ticketlock_classic create_ticketlock_classic();
/*@
requires
    exists<pair<level, predicate()> >(pair(?level, ?inv)) &*&
    ticketlock_classic_nb_level_dims <= level_subspace_nb_dims(level) &*&
    inv();
@*/
//@ ensures ticketlock_classic(result, level, inv);

/*@

predicate ticketlock_classic_held(ticketlock_classic lock, level level, predicate() inv, real frac, pair<void *, level> ob);

@*/
void ticketlock_classic_acquire(ticketlock_classic lock);
//@ requires obs(?p, ?obs) &*& [?f]ticketlock_classic(lock, ?level, ?inv) &*& forall(map(snd, obs), (all_sublevels_lt)(ticketlock_classic_nb_level_dims, level)) == true;
//@ ensures obs(?p1, cons(?ob, obs)) &*& is_ancestor_of(p, p1) == true &*& ticketlock_classic_held(lock, level, inv, f, ob) &*& inv() &*& level_lt(level, level_of(ob)) == true;

void ticketlock_classic_release(ticketlock_classic lock);
//@ requires obs(?p, ?obs) &*& ticketlock_classic_held(lock, ?level, ?inv, ?f, ?ob) &*& mem(ob, obs) == true &*& inv();
//@ ensures obs(p, remove(ob, obs)) &*& [f]ticketlock_classic(lock, level, inv);

void ticketlock_classic_dispose(ticketlock_classic lock);
//@ requires ticketlock_classic(lock, ?level, ?inv);
//@ ensures inv();

#endif
