// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#include <stdlib.h>
//@ #include <quantifiers.gh>
#include "busywaiting.h"
#include "atomics.h"
#include "ticketlock.h"
#include "ticketlock_strong.h"

typedef struct ticketlock {
    ticketlock_strong innerLock;
} *ticketlock;

/*@

lemma void ticketlock_M_nb_dims_nonneg()
    requires true;
    ensures 0 <= ticketlock_M_nb_dims;
{}

predicate ticketlock(ticketlock lock; predicate(int, bool) inv) =
    malloc_block_ticketlock(lock) &*&
    lock->innerLock |-> ?innerLock &*&
    ticketlock_strong(innerLock, inv);

predicate ticketlock_held(ticketlock lock, predicate(int, bool) inv, real f, int ticket) =
    [f]malloc_block_ticketlock(lock) &*&
    [f]lock->innerLock |-> ?innerLock &*& ticketlock_strong_locked(innerLock, inv, f, ticket);

@*/


ticketlock create_ticketlock()
//@ requires exists<predicate(int, bool)>(?inv) &*& inv(0, false);
//@ ensures ticketlock(result, inv);
//@ terminates;
{
    //@ open exists(_);
    ticketlock result = malloc(sizeof(struct ticketlock));
    if (result == 0) abort();
    //@ close exists(inv);
    ticketlock_strong innerLock = create_ticketlock_strong();
    result->innerLock = innerLock;
    return result;
}

void ticketlock_acquire(ticketlock lock)
/*@
requires
    [?f]ticketlock(lock, ?inv) &*&
    obs(?p, ?obs) &*& forall(map(snd, obs), (func_lt_level)(ticketlock_acquire)) == true &*&
    is_ticketlock_wait_ghost_op(?wop, inv, ?wait_inv, currentThread) &*&
    is_ticketlock_acquire_ghost_op(?aop, inv, wait_inv, ?post, currentThread) &*&
    wait_inv(-1, _, p, obs);
@*/
//@ ensures ticketlock_held(lock, inv, f, ?ticket) &*& post(ticket);
//@ terminates;
{
    //@ produce_func_lt(ticketlock_strong_acquire);
    //@ produce_func_lt(ticketlock_strong_dispose);
    {
        /*@
        predicate wait_inv_(int oldOwner, int oldM) =
            obs(p, ?obs1) &*& (oldOwner == -1 ? wait_inv(oldOwner, _, p, obs1) : wait_inv(oldOwner, {oldM}, p, obs1)) &*&
            is_ticketlock_wait_ghost_op(wop, inv, wait_inv, currentThread) &*&
            is_ticketlock_acquire_ghost_op(aop, inv, wait_inv, post, currentThread);
        predicate post_(int ticket) = post(ticket);
        @*/
        /*@
        produce_lemma_function_pointer_chunk ticketlock_strong_wait_ghost_op(inv, wait_inv_, currentThread)(M) {
            assert inv(?owner, ?held);
            assert atomic_spaces(?spaces);
            open wait_inv_(?oldOwner, ?oldM);
            is_ancestor_of_refl(p);
            if (!forall(map(fst, spaces), (func_gt)(ticketlock_dispose))) {
                void *badFunc = not_forall(map(fst, spaces), (func_gt)(ticketlock_dispose));
                forall_elim(map(fst, spaces), (func_gt)(ticketlock_strong_dispose), badFunc);
                assert false;
            }
            wop({M});
            call_perm__weaken(ticketlock_acquire, ticketlock_strong_acquire);
            close wait_inv_(owner, M);
        };
        @*/
        /*@
        produce_lemma_function_pointer_chunk ticketlock_strong_acquire_ghost_op(inv, wait_inv_, post_)() {
            open wait_inv_(_, _);
            assert atomic_spaces(?spaces);
            is_ancestor_of_refl(p);
            if (!forall(map(fst, spaces), (func_gt)(ticketlock_dispose))) {
                void *badFunc = not_forall(map(fst, spaces), (func_gt)(ticketlock_dispose));
                forall_elim(map(fst, spaces), (func_gt)(ticketlock_strong_dispose), badFunc);
                assert false;
            }
            aop();
            leak is_ticketlock_wait_ghost_op(wop, inv, wait_inv, _);
            leak is_ticketlock_acquire_ghost_op(aop, inv, wait_inv, post, _);
            close post_(_);
        };
        @*/
        //@ close wait_inv_(-1, -1);
        ticketlock_strong_acquire(lock->innerLock);
        //@ open post_(?ticket);
        //@ close ticketlock_held(lock, inv, f, ticket);
    }
}

void ticketlock_release(ticketlock lock)
/*@
requires
    obs(?p, ?obs) &*& forall(map(snd, obs), (func_lt_level)(ticketlock_acquire)) == true &*&
    ticketlock_held(lock, ?inv, ?f, ?ticket) &*& is_ticketlock_release_ghost_op(?ghop, inv, ticket, p, obs, ?pre, ?post, currentThread) &*& pre();
@*/
//@ ensures obs(?p2, ?obs1) &*& post(?p1, obs1) &*& is_ancestor_of(p1, p2) == true &*& [f]ticketlock(lock, inv);
//@ terminates;
{
    //@ open ticketlock_held(lock, inv, f, ticket);
    //@ produce_func_lt(ticketlock_strong_dispose);
    {
        /*@
        predicate pre_() =
            obs(p, obs) &*&
            is_ticketlock_release_ghost_op(ghop, inv, ticket, p, obs, pre, post, currentThread) &*& pre();
        predicate post_() =
            obs(p, ?obs1) &*&
            post(p, obs1);
        @*/
        /*@
        produce_lemma_function_pointer_chunk ticketlock_strong_release_ghost_op(inv, ticket, pre_, post_)() {
            open pre_();
            assert atomic_spaces(?spaces);
            if (!forall(map(fst, spaces), (func_gt)(ticketlock_dispose))) {
                void *badFunc = not_forall(map(fst, spaces), (func_gt)(ticketlock_dispose));
                forall_elim(map(fst, spaces), (func_gt)(ticketlock_strong_dispose), badFunc);
                assert false;
            }
            is_ancestor_of_refl(p);
            ghop();
            leak is_ticketlock_release_ghost_op(ghop, inv, ticket, p, obs, pre, post, _);
            close post_();
        };
        @*/
        //@ close pre_();
        ticketlock_strong_release(lock->innerLock);
        //@ open post_();
    }
    //@ is_ancestor_of_refl(p);
}

void ticketlock_dispose(ticketlock lock)
//@ requires ticketlock(lock, ?inv);
//@ ensures inv(_, false);
//@ terminates;
{
    ticketlock_strong_dispose(lock->innerLock);
    free(lock);
}
