// Justus Fasse and Bart Jacobs. Expressive modular deadlock-freedom verification. 2023.

#ifndef MUTEX_H
#define MUTEX_H

#include "futex.h"

struct mutex;
typedef struct mutex *mutex;

/*@

predicate mutex(mutex mutex; predicate(bool held) inv);
predicate mutex_held(mutex mutex, predicate(bool) inv, real frac);

@*/

mutex create_mutex();
//@ requires exists<predicate(bool)>(?inv) &*& inv(false);
//@ ensures mutex(result, inv);
//@ terminates;

/*@

typedef lemma void mutex_acquire_wait_op(list<level> obs, predicate() P, predicate() Q)(level level);
    requires [?f]ob(level) &*& forall(obs, (level_lt)(level)) == true &*& P();
    ensures [f]ob(level) &*& Q();

typedef lemma void mutex_acquire_wait_ghost_op(predicate(bool) inv, list<level> obs, predicate() waitInv)();
    requires inv(true) &*& is_mutex_acquire_wait_op(?wop, obs, ?P, ?Q) &*& P() &*& waitInv();
    ensures inv(true) &*& is_mutex_acquire_wait_op(wop, obs, P, Q) &*& Q() &*& waitInv();

typedef lemma void mutex_acquire_ghost_op(predicate(bool) inv, list<level> obs, predicate() waitInv, predicate() post)();
    requires obs(obs) &*& inv(false) &*& waitInv();
    ensures inv(true) &*& post();

@*/

void mutex_acquire(mutex mutex);
/*@
requires
    obs(?obs) &*& forall(obs, (func_lt_level)(mutex_release)) == true &*&
    [?f]mutex(mutex, ?inv) &*&
    is_mutex_acquire_wait_ghost_op(?wop, inv, obs, ?waitInv) &*&
    is_mutex_acquire_ghost_op(?aop, inv, obs, waitInv, ?post) &*&
    waitInv();
@*/
//@ ensures mutex_held(mutex, inv, f) &*& post();
//@ terminates;

/*@

typedef lemma void mutex_release_ghost_op(predicate(bool) inv, predicate() pre, predicate(list<level>) post)();
    requires inv(true) &*& pre();
    ensures inv(false) &*& post(?obs1) &*& obs(obs1);

@*/

void mutex_release(mutex mutex);
//@ requires mutex_held(mutex, ?inv, ?f) &*& is_mutex_release_ghost_op(?rop, inv, ?pre, ?post) &*& pre();
//@ ensures [f]mutex(mutex, inv) &*& post(?obs1) &*& obs(obs1);
//@ terminates;

void mutex_dispose(mutex mutex);
//@ requires mutex(mutex, ?inv);
//@ ensures inv(false);
//@ terminates;

#endif
