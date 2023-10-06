#include <stdlib.h>
#include "futex.h"
#include "mutex.h"
//@ #include <quantifiers.gh>
//@ #include "ghost_lists.gh"

struct mutex {
    int held_;
    //@ predicate(bool) inv_;
    //@ int internalThreadsGhostListId;
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

predicate_ctor mutex_inv(mutex mutex, predicate(bool) inv, int internalThreadsGhostListId)() =
    [1/2]mutex->held_ |-> ?held &*& (held == 0 ? mutex->heldFrac |-> _ &*& [1/2]mutex->held_ |-> held : held == 1 &*& [1/2]mutex->heldFrac |-> ?f &*& [f/2]mutex->internalThreadsGhostListId |-> _) &*&
    inv(held == 1) &*&
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
    atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId)) &*&
    futex(&mutex->held_, mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId));

predicate mutex_held(mutex mutex, predicate(bool) inv, real f) =
    [1/2]mutex->held_ |-> 1 &*&
    [1/2]mutex->heldFrac |-> f &*&
    [f]malloc_block_mutex(mutex) &*&
    [f]mutex->inv_ |-> inv &*&
    [f/2]mutex->internalThreadsGhostListId |-> ?internalThreadsGhostListId &*&
    [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId)) &*&
    [f]futex(&mutex->held_, mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId));

@*/

mutex create_mutex()
//@ requires exists<predicate(bool)>(?inv) &*& inv(false);
//@ ensures mutex(result, inv);
{
    //@ open exists(_);
    mutex mutex = malloc(sizeof(struct mutex));
    if (mutex == 0) abort();
    mutex->held_ = 0;
    //@ mutex->inv_ = inv;
    //@ mutex->nbWaiting = 0;
    //@ int internalThreadsGhostListId = create_ghost_list<unit>();
    //@ mutex->internalThreadsGhostListId = internalThreadsGhostListId;
    //@ close mutex_futex_inv(mutex)(0);
    //@ create_futex(&mutex->held_, mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId));
    //@ close n_obs(0);
    //@ close mutex_inv(mutex, inv, internalThreadsGhostListId)();
    //@ create_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
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
{
    //@ int internalThreadsGhostListId = mutex->internalThreadsGhostListId;
    //@ create_ob(L);
    /*@
    {
        predicate pre_() =
            ob(L) &*&
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
        predicate post_() =
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId)) &*&
            ghost_list_member_handle(internalThreadsGhostListId, unit);
        produce_lemma_function_pointer_chunk atomic_noop_ghost_op(pre_, post_)() {
            open pre_();
            open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
            open mutex_inv(mutex, inv, internalThreadsGhostListId)();
            
            assert ghost_list(internalThreadsGhostListId, ?internalThreadsList);
            ghost_list_insert(internalThreadsGhostListId, {}, internalThreadsList, unit);
            close n_obs(length(internalThreadsList) + 1);
            
            close mutex_inv(mutex, inv, internalThreadsGhostListId)();
            close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
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
        [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId)) &*&
        [f]futex(&mutex->held_, mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId)) &*&
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
                [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId)) &*& obs(cons(L, obs)) &*&
                is_mutex_acquire_ghost_op(aop, inv, obs, waitInv, post) &*& waitInv();
            predicate post_() =
                [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId)) &*&
                [1/2]mutex->held_ |-> 1 &*&
                [1/2]mutex->heldFrac |-> f &*&
                post();
            @*/
            /*@
            produce_lemma_function_pointer_chunk atomic_weak_compare_and_set_int_ghost_op(&mutex->held_, 0, 1, pre_, post_)() {
                open pre_();
                open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
                open mutex_inv(mutex, inv, internalThreadsGhostListId)();
                
                assert [_]mutex->held_ |-> ?held;
                assert is_atomic_weak_compare_and_set_int_op(?op, &mutex->held_, 0, 1, ?P, ?Q);
                op();
                
                if (held == 0) {
                    mutex->heldFrac = f;
                    open n_obs(_);
                    ghost_list_member_handle_lemma();
                    assert ghost_list(internalThreadsGhostListId, cons(?elem, ?internalThreadsList));
                    switch (elem) { case unit: }
                    ghost_list_remove(internalThreadsGhostListId, {}, internalThreadsList, unit);
                    discharge_ob(L);
                    aop();
                    leak is_mutex_acquire_ghost_op(aop, inv, obs, waitInv, post);
                }
                
                close mutex_inv(mutex, inv, internalThreadsGhostListId)();
                close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
                
                if (held == 0) {
                    close post_();
                } else {
                    close pre_();
                }
            };
            @*/
            //@ close pre_();
            success = atomic_weak_compare_and_set_int(&mutex->held_, 0, 1);
            if (success) {
                //@ open post_();
                //@ leak is_mutex_acquire_wait_ghost_op(wop, inv, obs, waitInv);
                break;
            } else {
                //@ open pre_();
            }
        }
        {
            /*@
            predicate pre_() =
                obs(cons(L, obs)) &*&
                ghost_list_member_handle(internalThreadsGhostListId, unit) &*&
                is_mutex_acquire_wait_ghost_op(wop, inv, obs, waitInv) &*& waitInv() &*&
                [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
            predicate waitInv_(list<level> obs_) =
                obs_ == obs &*&
                is_mutex_acquire_wait_ghost_op(wop, inv, obs, waitInv) &*& waitInv() &*&
                [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
            predicate post_(bool b) =
                obs(cons(L, obs)) &*&
                is_mutex_acquire_wait_ghost_op(wop, inv, obs, waitInv) &*& waitInv() &*&
                [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId)) &*&
                b ? true : ghost_list_member_handle(internalThreadsGhostListId, unit);
            @*/
            /*@
            produce_lemma_function_pointer_chunk futex_wait_enqueue_ghost_op(&mutex->held_, mutex_futex_inv(mutex), 1, pre_, waitInv_, post_)() {
                open pre_();
                open mutex_futex_inv(mutex)(?nbWaiting);
                open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
                open mutex_inv(mutex, inv, internalThreadsGhostListId)();
                
                assert is_futex_wait_enqueue_op(?op, &mutex->held_, ?P, ?Q);
                op();
                
                if (mutex->held_ == 1) {
                    nbWaiting++;
                    mutex->nbWaiting++;
                    close waitInv_(obs);
                    ghost_list_member_handle_lemma();
                    assert ghost_list(internalThreadsGhostListId, cons(?elem, ?internalThreadsList));
                    switch (elem) { case unit: }
                    ghost_list_remove(internalThreadsGhostListId, {}, internalThreadsList, elem);
                    open n_obs(_);
                    discharge_ob(L);
                } else {
                    close post_(false);
                }
                
                close mutex_inv(mutex, inv, internalThreadsGhostListId)();
                close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
                close mutex_futex_inv(mutex)(nbWaiting);
            };
            @*/
            /*@
            produce_lemma_function_pointer_chunk futex_wait_wait_ghost_op(mutex_futex_inv(mutex), waitInv_)() {
                open waitInv_(_);
                open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
                open mutex_inv(mutex, inv, internalThreadsGhostListId)();
                open mutex_futex_inv(mutex)(?nbWaiting);
                
                assert is_futex_wait_wait_op(?op, obs, ?P, ?Q);
                
                if (mutex->held_ == 1) {
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
                
                close mutex_inv(mutex, inv, internalThreadsGhostListId)();
                close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
                close waitInv_(obs);
                close mutex_futex_inv(mutex)(nbWaiting);
            };
            @*/
            /*@
            produce_lemma_function_pointer_chunk futex_wait_dequeue_ghost_op(mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId), waitInv_, post_)() {
                open mutex_futex_inv(mutex)(?nbWaiting);
                open waitInv_(_);
                open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
                open mutex_inv(mutex, inv, internalThreadsGhostListId)();
                
                mutex->nbWaiting--;
                create_ob(L);
                assert ghost_list(internalThreadsGhostListId, ?internalThreadsList);
                ghost_list_insert(internalThreadsGhostListId, {}, internalThreadsList, unit);
                close n_obs(length(internalThreadsList) + 1);
                
                close mutex_inv(mutex, inv, internalThreadsGhostListId)();
                close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
                close post_(true);
                close mutex_futex_inv(mutex)(nbWaiting - 1);
                close mutex_futex_dequeue_post(internalThreadsGhostListId)();
            };
            @*/
            //@ close pre_();
            futex_wait(&mutex->held_, 1);
            //@ open post_(?success_);
            //@ if (success_) open mutex_futex_dequeue_post(internalThreadsGhostListId)();
        }
    }
    //@ close mutex_held(mutex, inv, f);
}

void mutex_release(mutex mutex)
/*@
requires
    obs(?obs) &*& forall(obs, (func_lt_level)(mutex_release)) == true &*&
    mutex_held(mutex, ?inv, ?f) &*& is_mutex_release_ghost_op(?rop, inv, ?pre, ?post) &*& pre();
@*/
//@ ensures obs(obs) &*& [f]mutex(mutex, inv) &*& post();
{
    //@ open mutex_held(mutex, inv, f);
    //@ create_ob(L);
    //@ int internalThreadsGhostListId = mutex->internalThreadsGhostListId;
    {
        /*@
        predicate pre_() =
            ob(L) &*&
            [1/2]mutex->held_ |-> 1 &*&
            [1/2]mutex->heldFrac |-> f &*&
            is_mutex_release_ghost_op(rop, inv, pre, post) &*& pre() &*&
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
        predicate post_() =
            ghost_list_member_handle(internalThreadsGhostListId, unit) &*&
            post() &*&
            [f/2]mutex->internalThreadsGhostListId |-> _ &*&
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_int_ghost_op(&mutex->held_, 0, pre_, post_)() {
            open pre_();
            open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
            open mutex_inv(mutex, inv, internalThreadsGhostListId)();
            
            assert is_atomic_store_int_op(?op, _, _, _, _);
            op();
            
            assert ghost_list(internalThreadsGhostListId, ?internalThreadsList);
            ghost_list_insert(internalThreadsGhostListId, {}, internalThreadsList, unit);
            close n_obs(length(internalThreadsList) + 1);
            
            rop();
            leak is_mutex_release_ghost_op(_, _, _, _);
            
            close mutex_inv(mutex, inv, internalThreadsGhostListId)();
            close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
            close post_();
        };
        @*/
        //@ close pre_();
        atomic_store_int(&mutex->held_, 0);
        //@ open post_();
    }
    {
        /*@
        predicate pre_() =
            ghost_list_member_handle(internalThreadsGhostListId, unit) &*&
            obs(cons(L, obs)) &*&
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
        predicate post_() =
            obs(obs) &*&
            [f]atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
        @*/
        /*@
        produce_lemma_function_pointer_chunk futex_wake_one_ghost_op(mutex_futex_inv(mutex), mutex_futex_dequeue_post(internalThreadsGhostListId), pre_, post_)() {
            open pre_();
            open_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
            open mutex_inv(mutex, inv, internalThreadsGhostListId)();
            open mutex_futex_inv(mutex)(?nbWaiting);
            
            ghost_list_member_handle_lemma();
            assert ghost_list(internalThreadsGhostListId, cons(?elem, ?internalThreadsList));
            switch (elem) { case unit: }
            ghost_list_remove(internalThreadsGhostListId, {}, internalThreadsList, elem);
            open n_obs(_);
            discharge_ob(L);
            
            if (nbWaiting != 0) {
                open mutex_futex_dequeue_post(internalThreadsGhostListId)();
                ghost_list_member_handle_lemma();
                assert internalThreadsList == cons(_, _);
                close mutex_futex_dequeue_post(internalThreadsGhostListId)();
            }
            
            close mutex_inv(mutex, inv, internalThreadsGhostListId)();
            close_atomic_space(create_mutex, mutex_inv(mutex, inv, internalThreadsGhostListId));
            close post_();
            close mutex_futex_inv(mutex)(nbWaiting);
        };
        @*/
        //@ close pre_();
        futex_wake_one(&mutex->held_);
        //@ open post_();
    }
}

void mutex_dispose(mutex mutex)
//@ requires mutex(mutex, ?inv);
//@ ensures inv(false);
{
    //@ open mutex(mutex, inv);
    //@ destroy_futex(&mutex->held_);
    //@ int internalThreadsGhostListId = mutex->internalThreadsGhostListId;
    //@ open mutex_futex_inv(mutex)(?nbWaiting);
    //@ destroy_atomic_space();
    //@ open mutex_inv(mutex, inv, internalThreadsGhostListId)();
    free(mutex);
    //@ leak ghost_list(_, _);
    //@ leak n_obs(_);
}