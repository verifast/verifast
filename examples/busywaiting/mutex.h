// Tobias Reinhard and Bart Jacobs. Ghost signals: verifying termination of busy-waiting. 2020.

#ifndef MUTEX_H
#define MUTEX_H

#include "busywaiting.h"

//@ fixpoint int mutex_nb_level_dims();

/*@

lemma_auto void mutex_nb_level_dims_nonneg();
    requires true;
    ensures 0 <= mutex_nb_level_dims;

@*/

struct mutex;
typedef struct mutex *mutex;

//@ predicate mutex(mutex mutex; level level, predicate() inv);
//@ predicate locked(mutex mutex, level level, predicate() inv, real frac, pair<void *, level> ob);

mutex create_mutex();
//@ requires exists<level>(?level) &*& exists<predicate()>(?inv) &*& inv() &*& mutex_nb_level_dims <= level_subspace_nb_dims(level);
//@ ensures mutex(result, level, inv);
//@ terminates;

void acquire(mutex mutex);
//@ requires obs(?p, ?obs) &*& [?f]mutex(mutex, ?level, ?inv) &*& forall(map(snd, obs), (all_sublevels_lt)(mutex_nb_level_dims, level)) == true;
//@ ensures obs(p, cons(?ob, obs)) &*& locked(mutex, level, inv, f, ob) &*& inv() &*& level_lt(level, level_of(ob)) == true;
//@ terminates;

void release(mutex mutex);
//@ requires obs(?p, ?obs) &*& locked(mutex, ?level, ?inv, ?f, ?ob) &*& inv();
//@ ensures obs(p, remove(ob, obs)) &*& [f]mutex(mutex, level, inv);
//@ terminates;

/*@

typedef lemma void release_ghost_op(int tid, list<pathcomp> p, list<pair<void *, level> > obs, predicate() inv, predicate() pre, predicate() post)();
  requires obs(p, obs) &*& pre() &*& currentThread == tid;
  ensures obs(p, obs) &*& inv() &*& post();

@*/

void release_with_ghost_op(mutex mutex);
//@ requires obs(?p, ?obs) &*& locked(mutex, ?level, ?inv, ?f, ?ob) &*& is_release_ghost_op(_, currentThread, p, remove(ob, obs), inv, ?pre, ?post) &*& pre();
//@ ensures obs(p, remove(ob, obs)) &*& [f]mutex(mutex, level, inv) &*& post();
//@ terminates;

#endif
