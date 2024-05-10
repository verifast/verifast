// Justus Fasse and Bart Jacobs. Expressive modular deadlock-freedom verification. 2023.

#include <stdlib.h>
#include "futex.h"
#include "mutex.h"
//@ #include <quantifiers.gh>
//@ #include "ghost_lists.gh"

struct mutex {
    int held_;
    //@ predicate(bool) inv_;
    //@ int internalThreadsGhostListId;
    //@ int readersId;
    //@ int nbWaiting;
    //@ real heldFrac;
};

/*@

fixpoint level L() { return level(mutex_release, {}); }

predicate n_obs(int n) =
    n == 0 ?
        true
    :
        ob(L) &*& n_obs(n - 1);

/*
Invariant:
if any thread is blocked on the futex, then either the lock is held or there is at least one internal thread (i.e. busy acquiring or releasing).
*/

predicate_ctor mutex_inv(mutex mutex, predicate(bool) inv, int internalThreadsGhostListId, int readersId)() =
    [1/2]futex_word(&mutex->held_, ?held) &*& (held == 0 ? mutex->heldFrac |-> _ &*& [1/2]futex_word(&mutex->held_, held) : held == 1 &*& [1/2]mutex->heldFrac |-> ?f &*& [f/2]mutex->internalThreadsGhostListId |-> _) &*&
    inv(held == 1) &*&
    ghost_list<unit>(readersId, ?readers) &*& (held == 1 ? true : call_perms_(length(readers), mutex_acquire)) &*&
    [1/2]mutex->nbWaiting |-> ?nbWaiting &*& 0 <= nbWaiting &*&
    ghost_list<unit>(internalThreadsGhostListId, ?internalThreadsList) &*& n_obs(length(internalThreadsList)) &*&
    nbWaiting == 0 || held == 1 || internalThreadsList != {};

predicate_ctor mutex_futex_dequeue_post(int internalThreadsGhostListId)() = ghost_list_member_handle(internalThreadsGhostListId, unit);

predicate_ctor mutex_futex_inv(mutex mutex)(int nbWaiting) =
    [1/2]mutex->nbWaiting |-> nbWaiting;

predicate mutex(mutex mutex; predicate(bool held) inv) =
    malloc_block_mutex(mutex) &*&
    mutex->inv_ |-> inv &*&
    mutex->internalThreadsGhostListId |-> ?internalThreadsGhostListId &*&
    mutex->readersId |-> ?readersId &*&
    atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)) &*&
    futex(&mutex->held_, mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId), mutex_acquire);

predicate mutex_held(mutex mutex, predicate(bool) inv, real f) =
    [1/2]futex_word(&mutex->held_, 1) &*&
    [1/2]mutex->heldFrac |-> f &*&
    [f]malloc_block_mutex(mutex) &*&
    [f]mutex->inv_ |-> inv &*&
    [f/2]mutex->internalThreadsGhostListId |-> ?internalThreadsGhostListId &*&
    [f]mutex->readersId |-> ?readersId &*&
    [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)) &*&
    [f]futex(&mutex->held_, mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId), mutex_acquire);

@*/

mutex create_mutex()
//@ requires exists<predicate(bool)>(?inv) &*& inv(false);
//@ ensures mutex(result, inv);
//@ terminates;
{
    //@ open exists(_);
    mutex mutex = malloc(sizeof(struct mutex));
    if (mutex == 0) abort();
    mutex->held_ = 0;
    //@ mutex->inv_ = inv;
    //@ mutex->nbWaiting = 0;
    //@ int internalThreadsGhostListId = create_ghost_list<unit>();
    //@ mutex->internalThreadsGhostListId = internalThreadsGhostListId;
    //@ int readersId = create_ghost_list<unit>();
    //@ mutex->readersId = readersId;
    //@ close mutex_futex_inv(mutex)(0);
    //@ create_futex(&mutex->held_, mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId), mutex_acquire);
    //@ close n_obs(0);
    //@ close call_perms_(0, mutex_acquire);
    //@ close mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
    //@ create_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
    return mutex;
}

void mutex_acquire(mutex mutex)
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
{
    //@ int internalThreadsGhostListId = mutex->internalThreadsGhostListId;
    //@ int readersId = mutex->readersId;
    //@ create_ob(L);
    /*@
    {
        predicate pre_() =
            ob(L) &*&
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
        predicate post_() =
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)) &*&
            ghost_list_member_handle(internalThreadsGhostListId, unit);
        produce_lemma_function_pointer_chunk atomic_noop_ghost_op(pre_, post_)() {
            open pre_();
            open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
            open mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
            
            assert ghost_list(internalThreadsGhostListId, ?internalThreadsList);
            ghost_list_insert(internalThreadsGhostListId, {}, internalThreadsList, unit);
            close n_obs(length(internalThreadsList) + 1);
            
            close mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
            close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
            close post_();
        };
        close pre_();
        atomic_noop();
        leak is_atomic_noop_ghost_op(_, _, _);
        open post_();
    }
    @*/
    for (;;)
    /*@
    invariant
        obs(cons(L, obs)) &*&
        [f/2]mutex->internalThreadsGhostListId |-> _ &*&
        [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)) &*&
        [f]futex(&mutex->held_, mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId), mutex_acquire) &*&
        ghost_list_member_handle(internalThreadsGhostListId, unit) &*&
        is_mutex_acquire_wait_ghost_op(wop, inv, obs, waitInv) &*&
        is_mutex_acquire_ghost_op(aop, inv, obs, waitInv, post) &*&
        waitInv();
    @*/
    {
        bool success;
        {
            /*@
            predicate pre_() =
                ghost_list_member_handle(internalThreadsGhostListId, unit) &*&
                [f/2]mutex->internalThreadsGhostListId |-> _ &*&
                [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)) &*& obs(cons(L, obs)) &*&
                is_mutex_acquire_ghost_op(aop, inv, obs, waitInv, post) &*& waitInv();
            predicate post_(bool success_) =
                [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)) &*&
                success_ ?
                    [1/2]futex_word(&mutex->held_, 1) &*&
                    [1/2]mutex->heldFrac |-> f &*&
                    post()
                :
                    obs(cons(L, obs)) &*&
                    ghost_list_member_handle(internalThreadsGhostListId, unit) &*&
                    ghost_list_member_handle(readersId, unit) &*&
                    [f/2]mutex->internalThreadsGhostListId |-> _ &*&
                    is_mutex_acquire_ghost_op(aop, inv, obs, waitInv, post) &*& waitInv();
            @*/
            /*@
            produce_lemma_function_pointer_chunk atomic_weak_compare_and_set_futex_word_ghost_op(&mutex->held_, 0, 1, pre_, post_)() {
                open pre_();
                open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
                open mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
                
                assert [_]futex_word(&mutex->held_, ?held);
                assert is_atomic_weak_compare_and_set_futex_word_op(?op, &mutex->held_, 0, 1, ?P, ?Q);
                op();
                
                if (held == 0) {
                    leak call_perms_(_, _);
                    mutex->heldFrac = f;
                    open n_obs(_);
                    ghost_list_member_handle_lemma(internalThreadsGhostListId);
                    assert ghost_list(internalThreadsGhostListId, cons(?elem, ?internalThreadsList));
                    switch (elem) { case unit: }
                    ghost_list_remove(internalThreadsGhostListId, {}, internalThreadsList, unit);
                    discharge_ob(L);
                    aop();
                    leak is_mutex_acquire_ghost_op(aop, inv, obs, waitInv, post);
                } else {
                    assert ghost_list(readersId, ?readers);
                    ghost_list_insert(readersId, {}, readers, unit);
                }
                
                close mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
                close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
                
                if (held == 0) {
                    close post_(true);
                } else {
                    close post_(false);
                }
            };
            @*/
            //@ close pre_();
            success = atomic_weak_compare_and_set_futex_word(&mutex->held_, 0, 1);
            if (success) {
                //@ open post_(_);
                //@ leak is_mutex_acquire_wait_ghost_op(wop, inv, obs, waitInv);
                break;
            } else {
                //@ assert exists<bool>(?spurious);
                //@ if (spurious) { open pre_(); call_perm_top_weaken(mutex_acquire); } else open post_(false);
            }
        }
        //@ open exists<bool>(?spurious);
        {
            /*@
            predicate pre_() =
                obs(cons(L, obs)) &*&
                ghost_list_member_handle(internalThreadsGhostListId, unit) &*&
                (spurious ? call_perm_(_, mutex_acquire) : ghost_list_member_handle(readersId, unit)) &*&
                is_mutex_acquire_wait_ghost_op(wop, inv, obs, waitInv) &*& waitInv() &*&
                [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
            predicate waitInv_(list<level> obs_) =
                obs_ == obs &*&
                is_mutex_acquire_wait_ghost_op(wop, inv, obs, waitInv) &*& waitInv() &*&
                [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
            predicate post_(bool b) =
                obs(cons(L, obs)) &*&
                is_mutex_acquire_wait_ghost_op(wop, inv, obs, waitInv) &*& waitInv() &*&
                [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)) &*&
                call_perm_(_, mutex_acquire) &*&
                b ? true : ghost_list_member_handle(internalThreadsGhostListId, unit);
            @*/
            /*@
            produce_lemma_function_pointer_chunk futex_wait_enqueue_ghost_op(&mutex->held_, mutex_futex_inv(mutex), 1, pre_, waitInv_, post_)() {
                open pre_();
                open mutex_futex_inv(mutex)(?nbWaiting);
                open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
                open mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
                
                assert is_futex_wait_enqueue_op(?op, &mutex->held_, ?P, ?Q);
                op();
                
                assert [_]futex_word(&mutex->held_, ?held);
                if (held == 1) {
                    if (spurious)
                        leak call_perm_(_, mutex_acquire);
                    else
                        leak ghost_list_member_handle(readersId, unit);
                    nbWaiting++;
                    mutex->nbWaiting++;
                    close waitInv_(obs);
                    ghost_list_member_handle_lemma(internalThreadsGhostListId);
                    assert ghost_list(internalThreadsGhostListId, cons(?elem, ?internalThreadsList));
                    switch (elem) { case unit: }
                    ghost_list_remove(internalThreadsGhostListId, {}, internalThreadsList, elem);
                    open n_obs(_);
                    discharge_ob(L);
                } else {
                    if (!spurious) {
                        ghost_list_member_handle_lemma(readersId);
                        assert ghost_list(readersId, cons(?elem, ?readers));
                        switch (elem) { case unit: }
                        ghost_list_remove(readersId, {}, readers, elem);
                        open call_perms_(_, _);
                    }
                    close post_(false);
                }
                
                close mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
                close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
                close mutex_futex_inv(mutex)(nbWaiting);
            };
            @*/
            /*@
            produce_lemma_function_pointer_chunk futex_wait_wait_ghost_op(mutex_futex_inv(mutex), waitInv_)() {
                open waitInv_(_);
                open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
                open mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
                open mutex_futex_inv(mutex)(?nbWaiting);
                
                assert is_futex_wait_wait_op(?op, obs, ?P, ?Q);
                
                assert [_]futex_word(&mutex->held_, ?held);
                if (held == 1) {
                    predicate P_() = is_futex_wait_wait_op(op, obs, P, Q) &*& P();
                    predicate Q_() = is_futex_wait_wait_op(op, obs, P, Q) &*& Q();
                    produce_lemma_function_pointer_chunk mutex_acquire_wait_op(obs, P_, Q_)(level) {
                        open P_();
                        op();
                        close Q_();
                    } {
                        close P_();
                        wop();
                        open Q_();
                    }
                } else {
                    assert ghost_list(internalThreadsGhostListId, ?internalThreadsList);
                    assert internalThreadsList == cons(_, _);
                    open n_obs(?n);
                    if (!forall(obs, (level_lt)(L))) {
                        level badLevel = not_forall(obs, (level_lt)(L));
                        forall_elim(obs, (func_lt_level)(mutex_release), badLevel);
                        assert false;
                    }
                    op();
                    close n_obs(n);
                }
                
                close mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
                close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
                close waitInv_(obs);
                close mutex_futex_inv(mutex)(nbWaiting);
            };
            @*/
            /*@
            produce_lemma_function_pointer_chunk futex_wait_dequeue_ghost_op(mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId), mutex_acquire, waitInv_, post_)() {
                open mutex_futex_inv(mutex)(?nbWaiting);
                open waitInv_(_);
                open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
                open mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
                
                mutex->nbWaiting--;
                create_ob(L);
                assert ghost_list(internalThreadsGhostListId, ?internalThreadsList);
                ghost_list_insert(internalThreadsGhostListId, {}, internalThreadsList, unit);
                close n_obs(length(internalThreadsList) + 1);
                
                close mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
                close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
                close post_(true);
                close mutex_futex_inv(mutex)(nbWaiting - 1);
                close mutex_futex_dequeue_post(internalThreadsGhostListId)();
            };
            @*/
            //@ close pre_();
            futex_wait(&mutex->held_, 1);
            //@ open post_(?success_);
            //@ call_perm__transfer();
            //@ if (success_) open mutex_futex_dequeue_post(internalThreadsGhostListId)();
        }
    }
    //@ close mutex_held(mutex, inv, f);
}

void mutex_release(mutex mutex)
//@ requires mutex_held(mutex, ?inv, ?f) &*& is_mutex_release_ghost_op(?rop, inv, ?pre, ?post) &*& pre();
//@ ensures [f]mutex(mutex, inv) &*& post(?obs1) &*& obs(obs1);
//@ terminates;
{
    //@ open mutex_held(mutex, inv, f);
    //@ int internalThreadsGhostListId = mutex->internalThreadsGhostListId;
    //@ int readersId = mutex->readersId;
    //@ produce_call_below_perm_();
    {
        /*@
        predicate pre_() =
            call_below_perm_(currentThread, mutex_release) &*&
            [1/2]futex_word(&mutex->held_, 1) &*&
            [1/2]mutex->heldFrac |-> f &*&
            is_mutex_release_ghost_op(rop, inv, pre, post) &*& pre() &*&
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
        predicate post_() =
            ghost_list_member_handle(internalThreadsGhostListId, unit) &*&
            post(?obs1) &*&
            obs(cons(L, obs1)) &*&
            [f/2]mutex->internalThreadsGhostListId |-> _ &*&
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_futex_word_ghost_op(&mutex->held_, 0, pre_, post_)() {
            open pre_();
            open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
            open mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
            
            assert is_atomic_store_futex_word_op(?op, _, _, _, _);
            op();
            
            assert ghost_list(readersId, ?readers);
            call_below_perm__weaken(length(readers), mutex_acquire);
            
            rop();
            leak is_mutex_release_ghost_op(_, _, _, _);

            create_ob(L);
                        
            assert ghost_list(internalThreadsGhostListId, ?internalThreadsList);
            ghost_list_insert(internalThreadsGhostListId, {}, internalThreadsList, unit);
            close n_obs(length(internalThreadsList) + 1);
            
            close mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
            close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
            close post_();
        };
        @*/
        //@ close pre_();
        atomic_store_futex_word(&mutex->held_, 0);
        //@ open post_();
    }
    //@ assert post(?obs1);
    {
        /*@
        predicate pre_() =
            ghost_list_member_handle(internalThreadsGhostListId, unit) &*&
            obs(cons(L, obs1)) &*&
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
        predicate post_() =
            obs(obs1) &*&
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
        @*/
        /*@
        produce_lemma_function_pointer_chunk futex_wake_one_ghost_op(mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId), pre_, post_)() {
            open pre_();
            open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
            open mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
            open mutex_futex_inv(mutex)(?nbWaiting);
            
            ghost_list_member_handle_lemma(internalThreadsGhostListId);
            assert ghost_list(internalThreadsGhostListId, cons(?elem, ?internalThreadsList));
            switch (elem) { case unit: }
            ghost_list_remove(internalThreadsGhostListId, {}, internalThreadsList, elem);
            open n_obs(_);
            discharge_ob(L);
            
            if (nbWaiting != 0) {
                open mutex_futex_dequeue_post(internalThreadsGhostListId)();
                ghost_list_member_handle_lemma(internalThreadsGhostListId);
                assert internalThreadsList == cons(_, _);
                close mutex_futex_dequeue_post(internalThreadsGhostListId)();
            }
            
            close mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
            close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId, readersId));
            close post_();
            close mutex_futex_inv(mutex)(nbWaiting);
        };
        @*/
        //@ close pre_();
        //@ produce_call_below_perm_();
        //@ call_below_perm__weaken(1, mutex_acquire);
        //@ open call_perms_(_, _);
        //@ open call_perms_(_, _);
        //@ call_perm__transfer();
        futex_wake_one(&mutex->held_);
        //@ open post_();
    }
}

void mutex_dispose(mutex mutex)
//@ requires mutex(mutex, ?inv);
//@ ensures inv(false);
//@ terminates;
{
    //@ open mutex(mutex, inv);
    //@ int internalThreadsGhostListId = mutex->internalThreadsGhostListId;
    //@ int readersId = mutex->readersId;
    //@ destroy_atomic_space();
    //@ open mutex_inv(mutex, inv, internalThreadsGhostListId, readersId)();
    //@ destroy_futex(&mutex->held_);
    //@ open mutex_futex_inv(mutex)(?nbWaiting);
    free(mutex);
    //@ leak ghost_list(_, _);
    //@ leak n_obs(_);
    //@ leak call_perms_(_, _);
    //@ leak ghost_list(_, _);
}
