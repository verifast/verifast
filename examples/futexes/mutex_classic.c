// Justus Fasse and Bart Jacobs. Expressive modular deadlock-freedom verification. 2023.

#include <stdlib.h>
#include "mutex.h"
#include "mutex_classic.h"
//@ #include <quantifiers.gh>

struct mutex_classic {
    //@ level level;
    //@ predicate() inv_;
    mutex mutex;
};

/*@

predicate_ctor mutex_classic_inv(level level, predicate() inv)(bool held) =
    held ? ob(level) : inv();

predicate mutex_classic(mutex_classic mutex; level level, predicate() inv) =
    malloc_block_mutex_classic(mutex) &*&
    mutex->level |-> level &*&
    mutex->inv_ |-> inv &*&
    mutex->mutex |-> ?innerMutex &*&
    mutex(innerMutex, mutex_classic_inv(level, inv));

predicate mutex_classic_held(mutex_classic mutex, level level, predicate() inv, real f) =
    [f]malloc_block_mutex_classic(mutex) &*&
    [f]mutex->level |-> level &*&
    [f]mutex->inv_ |-> inv &*&
    [f]mutex->mutex |-> ?innerMutex &*&
    mutex_held(innerMutex, mutex_classic_inv(level, inv), f);

@*/

mutex_classic create_mutex_classic()
//@ requires exists<pair<level, predicate()> >(pair(?level, ?inv)) &*& inv();
//@ ensures mutex_classic(result, level, inv);
//@ terminates;
{
    //@ open exists(_);
    mutex_classic mutex = malloc(sizeof(struct mutex_classic));
    if (mutex == 0) abort();
    //@ mutex->level = level;
    //@ mutex->inv_ = inv;
    //@ close mutex_classic_inv(level, inv)(false);
    //@ close exists(mutex_classic_inv(level, inv));
    mutex innerMutex = create_mutex();
    mutex->mutex = innerMutex;
    return mutex;
}

void mutex_classic_acquire(mutex_classic mutex)
//@ requires [?f]mutex_classic(mutex, ?level, ?inv) &*& obs(?obs) &*& forall(obs, (level_lt)(level)) == true &*& forall(obs, (func_lt_level)(mutex_classic_acquire)) == true;
//@ ensures mutex_classic_held(mutex, level, inv, f) &*& inv() &*& obs(cons(level, obs));
//@ terminates;
{
    //@ produce_func_lt(mutex_release);
    /*@
    if (!forall(obs, (func_lt_level)(mutex_release))) {
        level badLevel = not_forall(obs, (func_lt_level)(mutex_release));
        forall_elim(obs, (func_lt_level)(mutex_classic_acquire), badLevel);
        assert false;
    }
    @*/
    {
        /*@
        predicate waitInv() = true;
        predicate post() =
            obs(cons(level, obs)) &*& inv();
        @*/
        /*@
        produce_lemma_function_pointer_chunk mutex_acquire_wait_ghost_op(mutex_classic_inv(level, inv), obs, waitInv)() {
            open mutex_classic_inv(level, inv)(true);
            assert is_mutex_acquire_wait_op(?op, obs, ?P, ?Q);
            op(level);
            close mutex_classic_inv(level, inv)(true);
        };
        @*/
        /*@
        produce_lemma_function_pointer_chunk mutex_acquire_ghost_op(mutex_classic_inv(level, inv), obs, waitInv, post)() {
            open waitInv();
            open mutex_classic_inv(level, inv)(false);
            create_ob(level);
            close mutex_classic_inv(level, inv)(true);
            close post();
        };
        @*/
        //@ close waitInv();
        mutex_acquire(mutex->mutex);
        //@ open post();
    }
    //@ close mutex_classic_held(mutex, level, inv, f);
}

void mutex_classic_release(mutex_classic mutex)
//@ requires mutex_classic_held(mutex, ?level, ?inv, ?f) &*& obs(cons(level, ?obs)) &*& inv();
//@ ensures [f]mutex_classic(mutex, level, inv) &*& obs(obs);
//@ terminates;
{
    //@ open mutex_classic_held(mutex, level, inv, f);
    {
        /*@
        predicate pre() = obs(cons(level, obs)) &*& inv();
        predicate post(list<level> obs1) = obs1 == obs;
        @*/
        /*@
        produce_lemma_function_pointer_chunk mutex_release_ghost_op(mutex_classic_inv(level, inv), pre, post)() {
            open pre();
            open mutex_classic_inv(level, inv)(true);
            discharge_ob(level);
            close mutex_classic_inv(level, inv)(false);
            close post(obs);
        };
        @*/
        //@ close pre();
        mutex_release(mutex->mutex);
        //@ open post(_);
    }
}

void mutex_classic_dispose(mutex_classic mutex)
//@ requires mutex_classic(mutex, ?level, ?inv);
//@ ensures inv();
//@ terminates;
{
    mutex_dispose(mutex->mutex);
    free(mutex);
    //@ open mutex_classic_inv(level, inv)(false);
}
