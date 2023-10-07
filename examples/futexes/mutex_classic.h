// Justus Fasse and Bart Jacobs. Expressive modular deadlock-freedom verification. 2023.

#ifndef MUTEX_CLASSIC_H
#define MUTEX_CLASSIC_H

#include "futex.h"

struct mutex_classic;
typedef struct mutex_classic *mutex_classic;

/*@

predicate mutex_classic(mutex_classic mutex; level level, predicate() inv);
predicate mutex_classic_held(mutex_classic mutex, level level, predicate() inv, real f);

@*/

mutex_classic create_mutex_classic();
//@ requires exists<pair<level, predicate()> >(pair(?level, ?inv)) &*& inv();
//@ ensures mutex_classic(result, level, inv);
//@ terminates;

void mutex_classic_acquire(mutex_classic mutex);
//@ requires [?f]mutex_classic(mutex, ?level, ?inv) &*& obs(?obs) &*& forall(obs, (level_lt)(level)) == true &*& forall(obs, (func_lt_level)(mutex_classic_acquire)) == true;
//@ ensures mutex_classic_held(mutex, level, inv, f) &*& inv() &*& obs(cons(level, obs));
//@ terminates;

void mutex_classic_release(mutex_classic mutex);
//@ requires mutex_classic_held(mutex, ?level, ?inv, ?f) &*& obs(cons(level, ?obs)) &*& inv();
//@ ensures [f]mutex_classic(mutex, level, inv) &*& obs(obs);
//@ terminates;

void mutex_classic_dispose(mutex_classic mutex);
//@ requires mutex_classic(mutex, ?level, ?inv);
//@ ensures inv();
//@ terminates;

#endif
