#ifndef MUTEX_H
#define MUTEX_H

#include "futex.h"

struct mutex;
typedef struct mutex *mutex;

/*@

predicate mutex(mutex mutex; predicate(int owner, bool held) inv);
predicate mutex_held(mutex mutex, predicate(int, bool) inv, real frac, int owner);

@*/

mutex create_mutex();
//@ requires exists<predicate(int, bool)>(?inv) &*& inv(0, false);
//@ ensures mutex(result, inv);

/*@

typedef lemma void mutex_acquire_wait_op(list<level> obs, predicate() P, predicate() Q)(level level);
    requires [?f]ob(level) &*& forall(obs, (level_lt)(level)) == true &*& P();
    ensures [f]ob(level) &*& Q();

typedef lemma void mutex_acquire_wait_ghost_op(predicate(int, bool) inv, list<level> obs, predicate() waitInv)();
    requires inv(?owner, true) &*& is_mutex_acquire_wait_op(?wop, obs, ?P, ?Q) &*& P() &*& waitInv();
    ensures inv(owner, true) &*& is_mutex_acquire_wait_op(wop, obs, P, Q) &*& Q() &*& waitInv();

typedef lemma void mutex_acquire_ghost_op(predicate(int, bool) inv, list<level> obs, predicate() waitInv, predicate(int) post)();
    requires obs(obs) &*& inv(?owner, false) &*& waitInv();
    ensures inv(owner, true) &*& post(owner);

@*/

void mutex_acquire(mutex mutex);
/*@
requires
    obs(?obs) &*& [?f]mutex(mutex, ?inv) &*&
    is_mutex_acquire_wait_ghost_op(?wop, inv, obs, ?waitInv) &*&
    is_mutex_acquire_ghost_op(?aop, inv, obs, waitInv, ?post) &*&
    waitInv();
@*/
//@ ensures mutex_held(mutex, inv, f, ?owner) &*& post(owner);

/*@

typedef lemma void mutex_release_ghost_op(predicate(int, bool) inv, int owner, predicate() pre, predicate() post)();
    requires inv(owner, true) &*& pre();
    ensures inv(owner + 1, false) &*& post();

@*/

void mutex_release(mutex mutex);
//@ requires mutex_held(mutex, ?inv, ?f, ?owner) &*& is_mutex_release_ghost_op(?rop, inv, owner, ?pre, ?post) &*& pre();
//@ ensures [f]mutex(mutex, inv) &*& post();

void mutex_dispose(mutex mutex);
//@ requires mutex(mutex, ?inv);
//@ ensures inv(_, false);

#endif
