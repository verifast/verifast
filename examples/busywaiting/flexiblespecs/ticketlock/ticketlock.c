// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#include <stdlib.h>
#include "busywaiting.h"
#include "atomics.h"
#include "ticketlock.h"
#include "ticketlock_strong.h"
//@ #include <quantifiers.gh>

typedef struct ticketlock {
    //@ level level;
    //@ predicate(int, bool) inv_;
    ticketlock_strong lock;
} *ticketlock;

/*@

lemma_auto void ticketlock_nb_level_dims_nonneg()
    requires true;
    ensures 0 <= ticketlock_nb_level_dims();
{}

predicate ticketlock(ticketlock lock; level level, predicate(int, bool) inv) =
    lock->level |-> level &*& lock->inv_ |-> inv &*& malloc_block_ticketlock(lock) &*&
    ticketlock_nb_level_dims <= level_subspace_nb_dims(level) &*&
    lock->lock |-> ?innerLock &*&
    ticketlock_strong(innerLock, inv);

predicate ticketlock_held(ticketlock lock, level level, predicate(int, bool) inv, real f, int ticket) =
    [f]lock->level |-> level &*& [f]lock->inv_ |-> inv &*& [f]malloc_block_ticketlock(lock) &*&
    ticketlock_nb_level_dims <= level_subspace_nb_dims(level) &*&
    [f]lock->lock |-> ?innerLock &*&
    ticketlock_strong_locked(innerLock, inv, f, ticket);

@*/


ticketlock create_ticketlock()
/*@
requires
    exists<pair<level, predicate(int, bool)> >(pair(?level, ?inv)) &*& inv(0, false) &*&
    ticketlock_nb_level_dims <= level_subspace_nb_dims(level);
@*/
//@ ensures ticketlock(result, level, inv);
//@ terminates;
{
    //@ open exists(_);
    ticketlock result = malloc(sizeof(struct ticketlock));
    if (result == 0) abort();
    //@ close exists(inv);
    ticketlock_strong innerLock = create_ticketlock_strong();
    result->lock = innerLock;
    //@ result->level = level;
    //@ result->inv_ = inv;
    return result;
}

void ticketlock_acquire(ticketlock lock)
/*@
requires
    [?f]ticketlock(lock, ?level, ?inv) &*&
    obs(?p, ?obs) &*& 
    forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, level)) == true &*&
    is_ticketlock_wait_ghost_op(?wop, level, inv, ?wait_inv, currentThread) &*&
    is_ticketlock_acquire_ghost_op(?aop, obs, level, inv, wait_inv, ?post, currentThread) &*&
    wait_inv(-1, _, p);
@*/
//@ ensures ticketlock_held(lock, level, inv, f, ?ticket) &*& post(ticket);
//@ terminates;
{
    //@ open ticketlock(lock, level, inv);
    //@ assert level == level(?levelFunc, cons(?level_max_length, ?level0));
    //@ produce_func_lt(ticketlock_strong_acquire);
    {
        /*@
        predicate waitInv(int oldOwner, int oldM) =
            is_ticketlock_wait_ghost_op(wop, level, inv, wait_inv, currentThread) &*&
            is_ticketlock_acquire_ghost_op(aop, obs, level, inv, wait_inv, post, currentThread) &*&
            obs(p, obs) &*&
            oldOwner == -1 ?
                wait_inv(-1, _, p) &*& call_below_perm_(currentThread, ticketlock_acquire)
            :
                wait_inv(oldOwner, ticketlock_strong_acquire, p) &*& call_below_perms(oldM, p, ticketlock_acquire);
        @*/
        /*@
        produce_lemma_function_pointer_chunk ticketlock_strong_wait_ghost_op(inv, waitInv, currentThread)(M) {
            open waitInv(?oldOwner, ?oldM);
            assert inv(?owner, true);
            if (oldOwner == -1) {
                pathize_call_below_perm__multi(M + 1);
                open call_below_perms(_, _, _);
            } else if (owner != oldOwner) {
                call_below_perms_weaken(M + 1);
                open call_below_perms(_, _, _);
            }
            if (!forall(map(snd, obs), (level_lt)(level))) {
                level badLevel = not_forall(map(snd, obs), (level_lt)(level));
                forall_elim(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, level), badLevel);
                assert badLevel == level(_, cons(?badLevel_max_length, ?badLevel0));
                lex0_subspace_lt_lex0_lt(level_max_length, level0, {}, badLevel0);
                assert false;
            }
            is_ancestor_of_refl(p);
            wop(ticketlock_strong_acquire);
            close waitInv(owner, M);
        };
        @*/
        /*@
        produce_lemma_function_pointer_chunk ticketlock_strong_acquire_ghost_op(inv, waitInv, post)() {
            open waitInv(?oldOwner, _);
            if (oldOwner == -1) {
                leak call_below_perm_(_, _);
            } else {
                leak call_below_perms(_, _, _);
            }
            leak is_ticketlock_wait_ghost_op(_, _, _, _, _);
            is_ancestor_of_refl(p);
            aop();
            leak is_ticketlock_acquire_ghost_op(_, _, _, _, _, _, _);
        };
        @*/
        //@ produce_call_below_perm_();
        //@ close waitInv(-1, -1);
        ticketlock_strong_acquire(lock->lock);
        //@ assert post(?ticket);
        //@ close ticketlock_held(lock, level, inv, f, ticket);
    }
}

void ticketlock_release(ticketlock lock)
//@ requires ticketlock_held(lock, ?level, ?inv, ?f, ?ticket) &*& is_ticketlock_release_ghost_op(?ghop, inv, ticket, ?pre, ?post) &*& pre();
//@ ensures [f]ticketlock(lock, level, inv) &*& post();
//@ terminates;
{
    //@ open ticketlock_held(lock, level, inv, f, ticket);
    {
        /*@
        predicate pre_() =
            is_ticketlock_release_ghost_op(ghop, inv, ticket, pre, post) &*& pre();
        @*/
        /*@
        produce_lemma_function_pointer_chunk ticketlock_strong_release_ghost_op(inv, ticket, pre_, post)() {
            open pre_();
            ghop();
            leak is_ticketlock_release_ghost_op(ghop, inv, ticket, pre, post);
        };
        @*/
        //@ close pre_();
        ticketlock_strong_release(lock->lock);
    }
}

void ticketlock_dispose(ticketlock lock)
//@ requires ticketlock(lock, ?level, ?inv);
//@ ensures inv(_, false);
//@ terminates;
{
    ticketlock_strong_dispose(lock->lock);
    free(lock);
}
