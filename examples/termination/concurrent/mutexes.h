#ifndef MUTEXES_H
#define MUTEXES_H

//@ #include "levels.gh"
//@ #include "obligations.gh"
//@ #include "obligation_spaces.gh"

struct mutex;
typedef struct mutex *mutex;

/*@

predicate mutex(mutex mutex; int space, int termScope, real spaceFrac, level level, predicate() inv);
predicate mutex_held(mutex mutex, int space, int termScope, real spaceFrac, level level, predicate() inv, real frac);

@*/

mutex create_mutex();
    //@ requires exists<real>(?fs) &*& [fs]obligation_space(?space, ?termScope) &*& exists<level>(?level) &*& exists<predicate()>(?inv) &*& inv();
    //@ ensures mutex(result, space, termScope, fs, level, inv);
    //@ terminates;

void mutex_acquire(mutex mutex);
    //@ requires [?f]mutex(mutex, ?space, ?termScope, ?fs, ?level, ?inv) &*& obspace_obligation_set(space, ?obs) &*& level_all_above(obs, level) == true;
    //@ ensures mutex_held(mutex, space, termScope, fs, level, inv, f) &*& obspace_obligation_set(space, cons(level, obs)) &*& inv();
    //@ terminates;

void mutex_release(mutex mutex);
    //@ requires mutex_held(mutex, ?space, ?termScope, ?fs, ?level, ?inv, ?f) &*& obspace_obligation_set(space, ?obs) &*& mem(level, obs) == true &*& inv();
    //@ ensures [f]mutex(mutex, space, termScope, fs, level, inv) &*& obspace_obligation_set(space, remove(level, obs));
    //@ terminates;

void mutex_dispose(mutex mutex);
    //@ requires mutex(mutex, ?space, ?termScope, ?fs, ?level, ?inv);
    //@ ensures [fs]obligation_space(space, termScope) &*& inv();
    //@ terminates;

#endif
