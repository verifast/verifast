// tab_size:4

// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#include <stdlib.h>
#include "atomics.h"
#include "ticketlock_strong.h"
//@ #include <listex.gh>
//@ #include <ghost_cells.gh>

/*@

box_class growing_list(list<int> xs) {
  invariant true;
  action noop();
    requires true;
    ensures xs == old_xs;
  action add(int elem);
    requires true;
    ensures xs == append(old_xs, {elem});
  handle_predicate has_at(int k, int x) {
    invariant 0 <= k && k < length(xs) && nth(k, xs) == x;
    preserved_by noop() {}
    preserved_by add(elem) {
      nth_append(old_xs, {elem}, k);
    }
  }
}

@*/

struct ticketlock_strong {
    unsigned long long next;
    unsigned long long owner;
    //@ predicate(int, bool) inv_;
    //@ box growingListId;
};

/*@

inductive thread_info = thread_info(real frac, predicate(int, int) waitInv, predicate(int) post, bool grabbed);

predicate waiting_threads(ticketlock_strong lock, predicate(int, bool) inv, list<int> cellIds, int index, int owner) =
    switch (cellIds) {
        case nil: return true;
        case cons(cellId, cellIds0): return
            [1/2]ghost_cell(cellId, thread_info(?frac, ?waitInv, ?post, false)) &*&
            [frac/2]lock->growingListId |-> _ &*&
            is_ticketlock_strong_acquire_ghost_op(_, inv, waitInv, post) &*&
            waitInv(?oldOwner, ?oldM) &*& oldOwner == -1 || oldOwner == owner && oldM == index - owner || oldM > index - owner &*&
            waiting_threads(lock, inv, cellIds0, index + 1, owner);
    };

predicate grabbed_cell(int cellId) = ghost_cell(cellId, thread_info(_, _, _, true));

predicate_ctor lock_inv(ticketlock_strong lock, predicate(int, bool) inv, box growingListId)() =
    [1/2]counter(&lock->owner, ?owner) &*&
    counter(&lock->next, ?next) &*&
    inv(owner, ?held) &*& 0 <= owner &*&
    growing_list(growingListId, ?cellIds) &*& next == length(cellIds) &*& (held ? owner + 1 : owner) <= next &*&
    foreach(take(owner, cellIds), grabbed_cell) &*&
    owner < length(cellIds) ?
        held &*&
        [1/2]ghost_cell(nth(owner, cellIds), thread_info(?frac, _, ?post, ?grabbed)) &*&
        (grabbed ? true : post(owner) &*& [1/2]counter(&lock->owner, owner)) &*&
        waiting_threads(lock, inv, drop(owner + 1, cellIds), owner + 1, owner) &*&
        [frac/2]lock->growingListId |-> _
    :
        [1/2]counter(&lock->owner, owner);

predicate ticketlock_strong(ticketlock_strong lock; predicate(int, bool) inv) =
    pointer_within_limits(&lock->owner) == true &*&
    malloc_block_ticketlock_strong(lock) &*&
    lock->inv_ |-> inv &*&
    lock->growingListId |-> ?growingListId &*&
    atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId));

predicate ticketlock_strong_locked(ticketlock_strong lock, predicate(int, bool) inv, real frac, int owner) =
    pointer_within_limits(&lock->owner) == true &*&
    [frac]malloc_block_ticketlock_strong(lock) &*&
    [frac]lock->inv_ |-> inv &*&
    [frac/2]lock->growingListId |-> ?growingListId &*&
    [frac]atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId)) &*&
    [1/2]counter(&lock->owner, owner) &*&
    // Everything below is just to avoid a bogus case where we have to leak `post(_)`
    exists(?cellHandleId) &*&
    has_at(cellHandleId, growingListId, owner, ?cellId) &*& [1/2]ghost_cell(cellId, thread_info(frac, ?waitInv, ?post, true));

@*/

ticketlock_strong create_ticketlock_strong()
//@ requires exists<predicate(int, bool)>(?inv) &*& inv(0, false);
//@ ensures ticketlock_strong(result, inv);
//@ terminates;
{
    ticketlock_strong lock = malloc(sizeof(struct ticketlock_strong));
    if (lock == 0) abort();
    lock->next = 0;
    lock->owner = 0;
    //@ lock->inv_ = inv;
    //@ create_counter(&lock->next);
    //@ create_counter(&lock->owner);
    //@ create_box growingListId = growing_list({});
    //@ lock->growingListId = growingListId;
    //@ close foreach({}, grabbed_cell);
    //@ close lock_inv(lock, inv, growingListId)();
    //@ create_atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId));
    return lock;
}

void ticketlock_strong_acquire(ticketlock_strong lock)
/*@
requires
    [?f]ticketlock_strong(lock, ?inv) &*&
    is_ticketlock_strong_wait_ghost_op(?waitOp, inv, ?waitInv, currentThread) &*&
    is_ticketlock_strong_acquire_ghost_op(?acqOp, inv, waitInv, ?post) &*&
    waitInv(-1, _);
@*/
//@ ensures ticketlock_strong_locked(lock, inv, f, ?owner) &*& post(owner);
//@ terminates;
{
    //@ box growingListId = lock->growingListId;
    //@ int cellId = create_ghost_cell(thread_info(f, waitInv, post, false));
    unsigned long long ticket;
    {
	    /*@
        predicate pre_() =
            is_ticketlock_strong_acquire_ghost_op(acqOp, inv, waitInv, post) &*& waitInv(-1, _) &*&
            ghost_cell(cellId, thread_info(f, waitInv, post, false)) &*&
            [f/2]lock->growingListId |-> growingListId &*&
            [f]atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId));
        predicate post_(int result) =
            [f]atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId)) &*&
            exists(?cellHandleId) &*& has_at(cellHandleId, growingListId, result, cellId) &*&
            exists(?alreadyOwner) &*&
            alreadyOwner ?
                [1/2]ghost_cell(cellId, thread_info(f, waitInv, post, true)) &*&
                [1/2]counter(&lock->owner, result) &*&
                post(result)
            :
                [1/2]ghost_cell(cellId, thread_info(f, waitInv, post, false));
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_fetch_and_increment_counter_ghost_op(&lock->next, pre_, post_, currentThread)() {
            open pre_();
            open_atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId));
            open lock_inv(lock, inv, growingListId)();
            assert [1/2]counter(&lock->owner, ?owner);
            assert counter(&lock->next, ?next);
            assert is_atomic_fetch_and_increment_counter_op(?op, &lock->next, ?P, ?Q);
            op();
            leak is_atomic_fetch_and_increment_counter_op(op, &lock->next, P, Q);
            consuming_box_predicate growing_list(growingListId, ?cellIds)
            perform_action add(cellId) {
              nth_append_r(cellIds, {cellId}, 0);
            }
            producing_box_predicate growing_list(append(cellIds, {cellId}))
            producing_fresh_handle_predicate has_at(next, cellId);
            assert has_at(?cellHandleId, growingListId, next, cellId);
            take_append(owner, cellIds, {cellId});
            if (owner == next) {
                acqOp();
                leak is_ticketlock_strong_acquire_ghost_op(acqOp, inv, waitInv, post);
                close waiting_threads(lock, inv, {}, owner + 1, owner);
                ghost_cell_mutate(cellId, thread_info(f, waitInv, post, true));
            } else {
                nth_append(cellIds, {cellId}, owner);
                {
                    lemma void iter()
                        requires
                            waiting_threads(lock, inv, ?cellIds0, ?index, owner) &*&
                            [1/2]ghost_cell(cellId, thread_info(f, waitInv, post, false)) &*&
                            [f/2]lock->growingListId |-> _ &*&
                            is_ticketlock_strong_acquire_ghost_op(_, inv, waitInv, post) &*&
                            waitInv(-1, _);
                        ensures
                            waiting_threads(lock, inv, append(cellIds0, {cellId}), index, owner);
                    {
                        open waiting_threads(lock, inv, cellIds0, index, owner);
                        if (cellIds0 == nil) {
                            close waiting_threads(lock, inv, {}, index + 1, owner);
                        } else {
                            iter();
                        }
                        close waiting_threads(lock, inv, append(cellIds0, {cellId}), index, owner);
                    }
                    iter();
                }
                drop_append_le(owner + 1, cellIds, {cellId});
            }
            close lock_inv(lock, inv, growingListId)();
            close_atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId));
            close exists(cellHandleId);
            close exists(owner == next);
            close post_(next);
        };
        @*/
        //@ close pre_();
        ticket = atomic_fetch_and_increment_counter(&lock->next);
        //@ open post_(ticket);
    }
    //@ open exists<handle>(?cellHandleId);
    //@ open exists(?alreadyOwner);
    for (;;)
    /*@
    invariant
        [f]atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId)) &*&
        is_ticketlock_strong_wait_ghost_op(waitOp, inv, waitInv, currentThread) &*&
        has_at(cellHandleId, growingListId, ticket, cellId) &*&
        alreadyOwner ?
    		[1/2]ghost_cell(cellId, thread_info(f, waitInv, post, true)) &*&
            [1/2]counter(&lock->owner, ticket) &*&
            post(ticket)
        :
			[1/2]ghost_cell(cellId, thread_info(f, waitInv, post, false));
    @*/
    {
        unsigned long long owner;
        {
            /*@
            predicate pre_() =
                is_ticketlock_strong_wait_ghost_op(waitOp, inv, waitInv, currentThread) &*&
				[f]atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId)) &*&
				has_at(cellHandleId, growingListId, ticket, cellId) &*&
				alreadyOwner ?
					[1/2]ghost_cell(cellId, thread_info(f, waitInv, post, true)) &*&
				    [1/2]counter(&lock->owner, ticket) &*&
				    post(ticket)
				:
					[1/2]ghost_cell(cellId, thread_info(f, waitInv, post, false));
            predicate post_(int result) =
                is_ticketlock_strong_wait_ghost_op(waitOp, inv, waitInv, currentThread) &*&
				[f]atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId)) &*&
				has_at(cellHandleId, growingListId, ticket, cellId) &*&
				result == ticket ?
					[1/2]ghost_cell(cellId, thread_info(f, waitInv, post, true)) &*&
				    [1/2]counter(&lock->owner, ticket) &*&
				    post(ticket)
				:
				    !alreadyOwner &*&
				    call_perm_(currentThread, ticketlock_strong_acquire) &*&
					[1/2]ghost_cell(cellId, thread_info(f, waitInv, post, false));
            @*/
            /*@
            produce_lemma_function_pointer_chunk atomic_load_counter_ghost_op(&lock->owner, pre_, post_, currentThread)() {
                open pre_();
                open_atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId));
                open lock_inv(lock, inv, growingListId)();
                
                assert [_]counter(&lock->owner, ?owner_);
                
                assert is_atomic_load_counter_op(?op, &lock->owner, ?P, ?Q);
                op();
                
                consuming_box_predicate growing_list(growingListId, ?cellIds)
                consuming_handle_predicate has_at(cellHandleId, ticket, cellId)
                perform_action noop() {}
                producing_handle_predicate has_at(cellHandleId, ticket, cellId);
                
                if (owner_ == ticket) {
                    merge_fractions ghost_cell(cellId, _);
                    ghost_cell_mutate(cellId, thread_info(f, waitInv, post, true));
                } else if (ticket < owner_) {
                    nth_take(ticket, owner_, cellIds);
                    mem_nth(ticket, take(owner_, cellIds));
                    foreach_remove(cellId, take(owner_, cellIds));
                    open grabbed_cell(cellId);
                    merge_fractions ghost_cell(cellId, _);
                    assert false;
                } else {
                    lemma void iter()
                        requires
                            waiting_threads(lock, inv, ?cellIds0, ?index, owner_) &*& index <= ticket &*& ticket - index < length(cellIds0) &*&
                            atomic_spaces({pair(create_ticketlock_strong, lock_inv(lock, inv, growingListId))}) &*&
			                is_ticketlock_strong_wait_ghost_op(waitOp, inv, waitInv, currentThread) &*&
			                inv(owner_, true) &*&
                            nth(ticket - index, cellIds0) == cellId &*&
                            [1/2]ghost_cell(cellId, thread_info(f, waitInv, post, false));
                        ensures
                            atomic_spaces({pair(create_ticketlock_strong, lock_inv(lock, inv, growingListId))}) &*&
			                is_ticketlock_strong_wait_ghost_op(waitOp, inv, waitInv, currentThread) &*&
			                inv(owner_, true) &*&
                            waiting_threads(lock, inv, cellIds0, index, owner_) &*& nth(ticket - index, cellIds0) == cellId &*&
                            [1/2]ghost_cell(cellId, thread_info(f, waitInv, post, false)) &*&
                            call_perm_(currentThread, ticketlock_strong_acquire);
                    {
                        open waiting_threads(lock, inv, cellIds0, index, owner_);
                        if (index == ticket) {
                            merge_fractions ghost_cell(cellId, _);
                            waitOp(index - owner_);
                        } else {
                            iter();
                        }
                        close waiting_threads(lock, inv, cellIds0, index, owner_);
                    }
                    nth_drop(ticket - owner_ - 1, owner_ + 1, cellIds);
                    iter();
                }
                
                close lock_inv(lock, inv, growingListId)();
                close_atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId));
                close post_(owner_);
            };
            @*/
            //@ close pre_();
            owner = atomic_load_counter(&lock->owner);
            //@ open post_(owner);
        }
        if (owner == ticket) {
            //@ close exists(cellHandleId);
            break;
        }
    }
    //@ leak is_ticketlock_strong_wait_ghost_op(_, _, _, _);
    //@ close ticketlock_strong_locked(lock, inv, f, ticket);
}

void ticketlock_strong_release(ticketlock_strong lock)
//@ requires ticketlock_strong_locked(lock, ?inv, ?f, ?owner) &*& is_ticketlock_strong_release_ghost_op(?relOp, inv, owner, ?pre, ?post) &*& pre();
//@ ensures [f]ticketlock_strong(lock, inv) &*& post();
//@ terminates;
{
    //@ open ticketlock_strong_locked(lock, inv, f, owner);
    //@ box growingListId = lock->growingListId;
    //@ open exists(?cellHandleId);
    //@ assert has_at(cellHandleId, growingListId, owner, ?cellId);
    unsigned long long ownerPlusOne = get_counter_plus_one(&lock->owner);
    {
        /*@
        predicate pre_() =
            is_ticketlock_strong_release_ghost_op(relOp, inv, owner, pre, post) &*& pre() &*&
			[f]atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId)) &*&
			has_at(cellHandleId, growingListId, owner, cellId) &*&
			[1/2]ghost_cell(cellId, thread_info(f, _, _, true)) &*&
		    [1/2]counter(&lock->owner, owner);
        predicate post_() =
			[f]atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId)) &*&
			[f/2]lock->growingListId |-> _ &*&
            post();
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_counter_ghost_op(&lock->owner, ownerPlusOne, pre_, post_, currentThread)() {
            open pre_();
            open_atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId));
            open lock_inv(lock, inv, growingListId)();
            
            assert is_atomic_store_counter_op(?op, &lock->owner, ownerPlusOne, ?P, ?Q);
            op();
            
            consuming_box_predicate growing_list(growingListId, ?cellIds)
            consuming_handle_predicate has_at(cellHandleId, owner, cellId)
            perform_action noop() {};
            
            relOp();
            leak is_ticketlock_strong_release_ghost_op(relOp, inv, owner, pre, post);
            
            merge_fractions ghost_cell(cellId, _);
            
            close foreach({}, grabbed_cell);
            close grabbed_cell(cellId);
            close foreach({cellId}, grabbed_cell);
            foreach_append(take(owner, cellIds), {cellId});
            take_plus_one(owner, cellIds);
            
            if (owner + 1 < length(cellIds)) {
                lemma void iter()
                    requires waiting_threads(lock, inv, ?cellIds0, ?index, owner) &*& owner + 1 < index;
                    ensures waiting_threads(lock, inv, cellIds0, index, owner + 1);
                {
                    open waiting_threads(lock, inv, cellIds0, index, owner);
                    if (cellIds0 != nil)
                        iter();
                    close waiting_threads(lock, inv, cellIds0, index, owner + 1);
                }
            
                drop_n_plus_one(owner + 1, cellIds);
                open waiting_threads(lock, inv, drop(owner + 1, cellIds), owner + 1, owner);
                assert is_ticketlock_strong_acquire_ghost_op(?acqOp, inv, ?waitInv, ?acqPost);
                acqOp();
                leak is_ticketlock_strong_acquire_ghost_op(acqOp, inv, waitInv, acqPost);
                iter();
            } else {
                open waiting_threads(lock, inv, {}, _, _);
            }
            
            close lock_inv(lock, inv, growingListId)();
            close_atomic_space(create_ticketlock_strong, lock_inv(lock, inv, growingListId));
            close post_();
        };
        @*/
        //@ close pre_();
        atomic_store_counter(&lock->owner, ownerPlusOne);
        //@ open post_();
    }
}

void ticketlock_strong_dispose(ticketlock_strong lock)
//@ requires ticketlock_strong(lock, ?inv);
//@ ensures inv(_, false);
//@ terminates;
{
    //@ open ticketlock_strong(lock, inv);
    //@ box growingListId = lock->growingListId;
    //@ destroy_atomic_space();
    //@ open lock_inv(lock, inv, growingListId)();
    //@ destroy_counter(&lock->owner);
    //@ destroy_counter(&lock->next);
    free(lock);
    //@ leak growing_list(growingListId, _);
    //@ leak foreach(_, grabbed_cell);
}
