#include <stdlib.h>
#include "ticketlock.h"
#include "ticketlock_classic.h"

typedef struct ticketlock_classic {
  ticketlock lock;
} *ticketlock_classic;

/*@

fixpoint int ticketlock_classic_nb_level_dims() { return ticketlock_nb_level_dims; }

predicate ticketlock_classic(ticketlock_classic lock; list<int> level, predicate() inv);

@*/

ticketlock_classic create_ticketlock_classic()
//@ requires exists<pair<list<int>, predicate()> >(pair(?level, ?inv)) &*& level == cons(?level_max_length, ?level0) &*& length(level0) + ticketlock_classic_nb_level_dims >= level_max_length;
//@ ensures ticketlock_classic(result, level, inv);
{
  ticketlock_classic result = malloc(sizeof(struct ticketlock_classic));
  if (result == 0) abort();
  ticketlock lock = create_ticketlock();
  result->lock = lock;
  return result;
}

/*@

predicate ticketlock_classic_held(ticketlock_classic lock; list<int> level, predicate() inv, real frac, pair<void *, list<int> > ob);

@*/
void ticketlock_classic_acquire(ticketlock_classic lock)
//@ requires obs(?p, ?obs) &*& [?f]ticketlock_classic(lock, ?level, ?inv) &*& forall(map(snd, obs), (all_sublevels_lt)(ticketlock_classic_nb_level_dims, level)) == true;
//@ ensures obs(p, cons(?ob, obs)) &*& ticketlock_classic_held(lock, level, inv, f, ob) &*& inv() &*& level_lt(level, level_of(ob)) == true;
{
  ticketlock_acquire(lock->lock);
}

void ticketlock_classic_release(ticketlock_classic lock)
//@ requires obs(?p, ?obs) &*& ticketlock_classic_held(lock, ?level, ?inv, ?f, ?ob) &*& inv();
//@ ensures obs(p, remove(ob, obs)) &*& [f]ticketlock_classic(lock, level, inv);
{
  ticketlock_release(lock->lock);
}

void ticketlock_classic_dispose(ticketlock_classic lock)
//@ requires ticketlock_classic(lock, ?level, ?inv);
//@ ensures inv();
{
  ticketlock_dispose(lock->lock);
  free(lock);
}
