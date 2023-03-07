#include <stdlib.h>
#include "spinlock.h"

typedef struct spinlock_classic {
  spinlock_t spinlock;
} *spinlock_classic_t;

/*@

predicate spinlock_classic(spinlock_classic_t spinlock; list<int> level, predicate(int, bool) inv);

@*/

spinlock_classic_t create_spinlock_classic()
//@ requires exists<pair<list<int>, pair<predicate(int, bool), int> > >(pair(?level, pair(?inv, ?acquireCredits))) &*& inv(acquireCredits, false);
//@ ensures spinlock_classic(result, level, inv);
{
  spinlock_classic_t result = malloc(sizeof(struct spinlock_classic));
  if (result == 0) abort();
  result->spinlock = create_spinlock();
  return result;
}

/*@

typedef lemma void spinlock_classic_acquire_ghost_op(predicate(int, bool) inv, predicate() pre, predicate() post);
    requires inv(?acquireCredits, false) &*& pre();
    ensures inv(acquireCredits - 1, true) &*& post() &*& 1 <= acquireCredits;

predicate spinlock_classic_held(spinlock_classic_t spinlock, real f, predicate(int, bool) inv, pair<void *, list<inv> > ob);

@*/

void spinlock_classic_acquire(spinlock_classic_t spinlock)
/*@
requires
    obs(?p, ?obs) &*& [?f]spinlock_classic(spinlock, ?level, ?inv) &*& is_spinlock_classic_acquire_ghost_op(?ghop, inv, ?pre, ?post) &*& pre() &*&
    forall(obs, (level_lt)(level)) == true;
@*/
//@ ensures obs(p, cons(?ob, obs)) &*& spinlock_classic_held(spinlock, f, inv, ob) &*& post() &*& level_of(ob) == level;
{
  {
    /*@
    predicate pre_() = true;
    predicate post_() = true;
    @*/
    /*@
    
    @*/
    spinlock_acquire(spinlock->spinlock);
  }
}

void spinlock_classic_release(spinlock_classic_t spinlock)
//@ requires obs(?p, cons(?ob, ?obs)) &*& spinlock_classic_held(spinlock, ?f, ?inv, ob);
//@ ensures obs(p, obs) &*& [f]spinlock(spinlock, level_of(ob), inv);
{
  spinlock_release(spinlock->spinlock);
}
