// Tobias Reinhard and Bart Jacobs. Ghost signals: verifying termination of busy-waiting. 2020.
// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#include <stdlib.h>
#include "atomics.h"
#include "clhlock.h"
#include "clhlock_as_ticketlock.h"
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

box_class incr_box(int i) {
  invariant true;
  action noop();
    requires true;
    ensures i == old_i;
  action incr();
    requires true;
    ensures i == old_i + 1;
  handle_predicate is_lower_bound(int j) {
    invariant j <= i;
    preserved_by noop() {}
    preserved_by incr() {}
  }
}

@*/

struct lock {
    struct clhlock_as_ticketlock *innerLock;
    //@ box growingListId;
    //@ box incrBoxId;
};

struct lock_thread {
    struct clhlock_as_ticketlock_thread *innerThread;
};

/*@

predicate_ctor cell_pred(level level)(int cellId) = [1/2]ghost_cell(cellId, ?signalId) &*& signal(signalId, level, false); 

predicate_ctor lock_inv(struct lock *lock, level level, predicate() inv, box growingListId, box incrBoxId)(int owner, int nextTicket, bool held) =
    incr_box(incrBoxId, owner) &*&
    growing_list(growingListId, ?cellIds) &*& length(cellIds) == nextTicket &*&
    0 <= owner &*& (held ? owner + 1 : owner) <= nextTicket &*&
    (
        owner < nextTicket ?
            [_]ghost_cell(nth(owner, cellIds), ?ownerSignal) &*& signal(ownerSignal, level, false) &*&
            foreach(drop(owner + 1, cellIds), cell_pred(level))
        :
            true
    ) &*&
    held ?
        true
    :
        inv();

predicate lock(struct lock *lock, level level, predicate() inv;) =
    lock->growingListId |-> ?growingListId &*&
    lock->incrBoxId |-> ?incrBoxId &*&
    lock->innerLock |-> ?innerLock &*&
    clhlock_as_ticketlock(innerLock, lock_inv(lock, level, inv, growingListId, incrBoxId)) &*&
    malloc_block_lock(lock);

predicate lock_thread(struct lock_thread *thread) =
    thread->innerThread |-> ?innerThread &*& clhlock_as_ticketlock_thread(innerThread) &*&
    malloc_block_lock_thread(thread);

predicate locked(struct lock_thread *thread, struct lock *lock, level level, predicate() inv, real frac, pair<void *, level> ob) =
    thread->innerThread |-> ?innerThread &*&
    malloc_block_lock_thread(thread) &*&
    [frac]lock->growingListId |-> ?growingListId &*&
    [frac]lock->incrBoxId |-> ?incrBoxId &*&
    [frac]lock->innerLock |-> ?innerLock &*&
    clhlock_as_ticketlock_locked(innerThread, innerLock, lock_inv(lock, level, inv, growingListId, incrBoxId), frac, ?ticket) &*&
    exists(?cellHandleId) &*& has_at(cellHandleId, growingListId, ticket, ?cellId) &*& [_]ghost_cell<void *>(cellId, ?signalId) &*& ob == pair(signalId, level) &*&
    [frac]malloc_block_lock(lock);

@*/

struct lock *create_lock()
    //@ requires exists<level>(?level) &*& exists<predicate()>(?inv) &*& inv();
    //@ ensures lock(result, level, inv);
    //@ terminates;
{
    //@ open exists(_);
    //@ open exists(_);
    struct lock *lock = malloc(sizeof(struct lock));
    if (lock == 0) abort();
    //@ create_box growingListId = growing_list({});
    //@ create_box incrBoxId = incr_box(0);
    //@ lock->growingListId = growingListId;
    //@ lock->incrBoxId = incrBoxId;
    //@ close exists(lock_inv(lock, level, inv, growingListId, incrBoxId));
    //@ close lock_inv(lock, level, inv, growingListId, incrBoxId)(0, 0, false);
    struct clhlock_as_ticketlock *innerLock = create_clhlock_as_ticketlock();
    lock->innerLock = innerLock;
    return lock;
}

struct lock_thread *create_lock_thread()
    //@ requires true;
    //@ ensures lock_thread(result);
    //@ terminates;
{
    struct lock_thread *thread = malloc(sizeof(struct lock_thread));
    if (thread == 0) abort();
    struct clhlock_as_ticketlock_thread *innerThread = create_clhlock_as_ticketlock_thread();
    thread->innerThread = innerThread;
    return thread;
    //@ close lock_thread(thread);
}

/*@

lemma void drop_append_le<t>(int n, list<t> xs, list<t> ys)
    requires 0 <= n &*& n <= length(xs);
    ensures drop(n, append(xs, ys)) == append(drop(n, xs), ys);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (0 < n)
                drop_append_le(n - 1, xs0, ys);
    }
}

@*/

void acquire(struct lock_thread *thread, struct lock *lock)
    //@ requires obs(?p, ?obs) &*& lock_thread(thread) &*& [?frac]lock(lock, ?level, ?inv) &*& forall(map(snd, obs), (level_lt)(level)) == true;
    //@ ensures locked(thread, lock, level, inv, frac, ?ob) &*& inv() &*& obs(?p1, cons(ob, obs)) &*& is_ancestor_of(p, p1) == true &*& level_of(ob) == level;
    //@ terminates;
{
    //@ open lock_thread(thread);
    //@ open lock(lock, level, inv);
    //@ box growingListId = lock->growingListId;
    //@ box incrBoxId = lock->incrBoxId;
    //@ int cellId = create_ghost_cell<void *>(0);
    //@ produce_call_below_perm_();
    //@ produce_func_lt(clhlock_as_ticketlock_acquire);
    {
        /*@
        predicate pre() =
            call_below_perm_(currentThread, acquire) &*&
            obs(p, obs) &*&
            ghost_cell<void *>(cellId, 0);
        predicate wait_inv(int ticket, void *f) =
            exists<pair<handle, handle> >(pair(?lbHandleId, ?cellHandleId)) &*&
            is_lower_bound(lbHandleId, incrBoxId, ?oldOwner) &*& func_lt(f, acquire) == true &*&
            exists<option<handle> >(?startedWaiting) &*&
            switch (startedWaiting) {
                case none: return call_below_perms(ticket - oldOwner, p, acquire);
                case some(ownerHandleId): return
                    call_below_perms(ticket - oldOwner - 1, p, acquire) &*&
                    has_at(ownerHandleId, growingListId, oldOwner, ?ownerCell) &*& [_]ghost_cell(ownerCell, ?ownerSignalId) &*&
                    wait_perm(p, ownerSignalId, level, f);
            } &*&
            has_at(cellHandleId, growingListId, ticket, cellId) &*& [1/2]ghost_cell(cellId, ?signalId) &*& obs(p, cons(pair(signalId, level), obs));
        predicate post(int ticket) =
            exists(?cellHandleId) &*&
            has_at(cellHandleId, growingListId, ticket, cellId) &*& [_]ghost_cell(cellId, ?signalId) &*& obs(p, cons(pair(signalId, level), obs)) &*&
            inv();
        @*/
        /*@
        produce_lemma_function_pointer_chunk clhlock_as_ticketlock_get_ticket_ghost_op(lock_inv(lock, level, inv, growingListId, incrBoxId), pre, wait_inv, currentThread)(f) {
            open lock_inv(lock, level, inv, growingListId, incrBoxId)(?owner, ?nextTicket, ?held);
            open pre();
            pathize_call_below_perm__multi(nextTicket - owner);
            consuming_box_predicate incr_box(incrBoxId, owner)
            perform_action noop() {}
            producing_fresh_handle_predicate is_lower_bound(owner);
            assert is_lower_bound(?lbHandleId, incrBoxId, owner);
            consuming_box_predicate growing_list(growingListId, ?cellIds)
            perform_action add(cellId) {
              nth_append_r(cellIds, {cellId}, 0);
            }
            producing_box_predicate growing_list(append(cellIds, {cellId}))
            producing_fresh_handle_predicate has_at(nextTicket, cellId);
            assert has_at(?cellHandleId, growingListId, nextTicket, cellId);
            void *signalId = create_signal();
            init_signal(signalId, level);
            ghost_cell_mutate(cellId, signalId);
            close exists(pair(lbHandleId, cellHandleId));
            close exists(none);
            close wait_inv(nextTicket, f);
            if (owner < nextTicket) {
                nth_append(cellIds, {cellId}, owner);
                drop_append_le(owner + 1, cellIds, {cellId});
                close foreach({}, cell_pred(level));
                close cell_pred(level)(cellId);
                close foreach({cellId}, cell_pred(level));
                foreach_append(drop(owner + 1, cellIds), {cellId});
            } else {
                leak [_]ghost_cell(cellId, _);
                close foreach({}, cell_pred(level));
                drop_length(append(cellIds, {cellId}));
            }
            close lock_inv(lock, level, inv, growingListId, incrBoxId)(owner, nextTicket + 1, held);
        };
        @*/
        /*@
        produce_lemma_function_pointer_chunk clhlock_as_ticketlock_wait_ghost_op(lock_inv(lock, level, inv, growingListId, incrBoxId), wait_inv, currentThread)() {
            open lock_inv(lock, level, inv, growingListId, incrBoxId)(?owner, ?nextTicket, ?held);
            open wait_inv(?ticket, ?f);
            open exists(pair(?lbHandleId, ?cellHandleId));
            open exists<option<handle> >(?startedWaiting);
            assert has_at(cellHandleId, growingListId, ticket, cellId) &*& [1/2]ghost_cell(cellId, ?oldSignalId);
            consuming_box_predicate growing_list(growingListId, ?cellIds)
            consuming_handle_predicate has_at(cellHandleId, ticket, cellId)
            perform_action noop() {}
            producing_handle_predicate has_at(cellHandleId, ticket, cellId);
            nth_drop(ticket - owner - 1, owner + 1, cellIds);
            mem_nth(ticket - owner - 1, drop(owner + 1, cellIds));
            foreach_remove(cellId, drop(owner + 1, cellIds));
            open cell_pred(level)(cellId);
            set_signal(oldSignalId);
            leak signal(oldSignalId, level, true);
            assert [_]ghost_cell(nth(owner, cellIds), ?ownerSignal);
            consuming_box_predicate incr_box(incrBoxId, owner)
            consuming_handle_predicate is_lower_bound(lbHandleId, ?oldOwner)
            perform_action noop() {}
            producing_handle_predicate is_lower_bound(lbHandleId, owner);
            if (oldOwner == owner) {
                switch (startedWaiting) {
                    case none:
                        open call_below_perms(ticket - oldOwner, p, acquire);
                        consuming_box_predicate growing_list(growingListId, cellIds)
                        perform_action noop() {}
                        producing_fresh_handle_predicate has_at(owner, nth(owner, cellIds));
                        assert has_at(?ownerHandleId, growingListId, owner, nth(owner, cellIds));
                        create_wait_perm(ownerSignal, level, f);
                        close exists(some(ownerHandleId));
                    case some(ownerHandleId):
                        consuming_box_predicate growing_list(growingListId, cellIds)
                        consuming_handle_predicate has_at(ownerHandleId, owner, _)
                        perform_action noop() {}
                        producing_handle_predicate has_at(ownerHandleId, owner, nth(owner, cellIds));
                        merge_fractions ghost_cell(nth(owner, cellIds), _);
                        close exists(some(ownerHandleId));
                }
            } else {
                switch (startedWaiting) {
                    case none:
                    case some(oldOwnerHandleId):
                        leak
                            has_at(oldOwnerHandleId, growingListId, oldOwner, ?oldOwnerCell) &*& [_]ghost_cell(oldOwnerCell, ?oldOwnerSignalId) &*&
                            wait_perm(p, oldOwnerSignalId, level, f);
                }
                call_below_perms_weaken(ticket - owner);
                open call_below_perms(ticket - owner, p, acquire);
                consuming_box_predicate growing_list(growingListId, cellIds)
                perform_action noop() {}
                producing_fresh_handle_predicate has_at(owner, nth(owner, cellIds));
                assert has_at(?ownerHandleId, growingListId, owner, nth(owner, cellIds));
                create_wait_perm(ownerSignal, level, f);
                close exists(some(ownerHandleId));
            }
            is_ancestor_of_refl(p);
            wait(ownerSignal);
            void *newSignalId = create_signal();
            init_signal(newSignalId, level);
            ghost_cell_mutate(cellId, newSignalId);
            close cell_pred(level)(cellId);
            foreach_unremove(cellId, drop(owner + 1, cellIds));
            close lock_inv(lock, level, inv, growingListId, incrBoxId)(owner, nextTicket, held);
            close exists(pair(lbHandleId, cellHandleId));
            close wait_inv(ticket, f);
        };
        @*/
        /*@
        produce_lemma_function_pointer_chunk clhlock_as_ticketlock_acquire_ghost_op(lock_inv(lock, level, inv, growingListId, incrBoxId), wait_inv, post, currentThread)() {
            open lock_inv(lock, level, inv, growingListId, incrBoxId)(?owner, ?nextTicket, false);
            open wait_inv(owner, ?f);
            open exists(pair(?lbHandleId, ?cellHandleId));
            open exists(?startedWaiting);
            leak call_below_perms(_, _, _);
            leak is_lower_bound(lbHandleId, incrBoxId, ?oldOwner);
            switch (startedWaiting) {
                case none:
                case some(oldOwnerHandleId):
                    leak has_at(oldOwnerHandleId, _, _, ?ownerCell) &*& [_]ghost_cell(ownerCell, ?ownerSignalId) &*& wait_perm(p, ownerSignalId, level, f);
            }
            leak [1/2]ghost_cell(cellId, ?signalId);
            close lock_inv(lock, level, inv, growingListId, incrBoxId)(owner, nextTicket, true);
            close exists(cellHandleId);
            close post(owner);
        };
        @*/
        //@ close pre();
        clhlock_as_ticketlock_acquire(thread->innerThread, lock->innerLock);
        //@ open post(?ticket);
        //@ open exists(?cellHandleId);
        //@ assert has_at(cellHandleId, growingListId, ticket, cellId) &*& [_]ghost_cell(cellId, ?signalId);
        //@ close exists(cellHandleId);
        //@ close locked(thread, lock, level, inv, frac, pair(signalId, level));
        //@ is_ancestor_of_refl(p);
    }
}

void release_with_ghost_op(struct lock_thread *thread)
    /*@
    requires
        locked(thread, ?lock, ?level, ?inv, ?frac, ?ob) &*& obs(?p, ?obs) &*& mem(ob, obs) == true &*&
        is_release_ghost_op(?rgo, currentThread, inv, p, remove(ob, obs), ?pre, ?post) &*& pre();
    @*/
    //@ ensures post(?p1) &*& obs(?p2, remove(ob, obs)) &*& lock_thread(thread) &*& [frac]lock(lock, level, inv) &*& is_ancestor_of(p1, p2) == true;
    //@ terminates;
{
    //@ int releaseThread = currentThread;
    //@ open locked(thread, lock, level, inv, frac, ob);
    //@ box growingListId = lock->growingListId;
    //@ box incrBoxId = lock->incrBoxId;
    //@ struct clhlock_as_ticketlock *innerLock = lock->innerLock;
    //@ struct clhlock_as_ticketlock_thread *innerThread = thread->innerThread;
    //@ assert clhlock_as_ticketlock_locked(innerThread, innerLock, _, frac, ?ticket);
    //@ assert exists(?cellHandleId) &*& has_at(cellHandleId, growingListId, ticket, ?cellId) &*& [_]ghost_cell(cellId, ?signalId);
    {
        /*@
        predicate pre_() =
            has_at(cellHandleId, growingListId, ticket, cellId) &*& [_]ghost_cell(cellId, signalId) &*&
            is_release_ghost_op(rgo, releaseThread, inv, p, remove(ob, obs), pre, post) &*& pre() &*&
            obs(p, obs);
        predicate post_() =
            obs(p, remove(ob, obs)) &*& post(p);
        @*/
        /*@
        produce_lemma_function_pointer_chunk clhlock_as_ticketlock_release_ghost_op(lock_inv(lock, level, inv, growingListId, incrBoxId), ticket, pre_, post_, currentThread)() {
            open lock_inv(lock, level, inv, growingListId, incrBoxId)(ticket, ?nextTicket, true);
            open pre_();
            consuming_box_predicate incr_box(incrBoxId, ticket)
            perform_action incr() {}
            producing_box_predicate incr_box(ticket + 1);
            consuming_box_predicate growing_list(growingListId, ?cellIds)
            consuming_handle_predicate has_at(cellHandleId, ticket, cellId)
            perform_action noop() {};
            merge_fractions ghost_cell(cellId, _);
            set_signal(signalId);
            leak signal(signalId, _, _);
            if (ticket + 1 < nextTicket) {
                drop_n_plus_one(ticket + 1, cellIds);
                open foreach(drop(ticket + 1, cellIds), cell_pred(level));
                nth_drop(0, ticket + 1, cellIds);
                open cell_pred(level)(nth(ticket + 1, cellIds));
                leak [1/2]ghost_cell(nth(ticket + 1, cellIds), ?nextOwnerSignalId);
            } else {
                open foreach(drop(ticket + 1, cellIds), cell_pred(level));
            }
            is_ancestor_of_refl(p);
            rgo();
            leak is_release_ghost_op(rgo, _, _, _, _, _, _);
            close lock_inv(lock, level, inv, growingListId, incrBoxId)(ticket + 1, nextTicket, false);
            close post_();
        };
        @*/
        //@ close pre_();
        clhlock_as_ticketlock_release(thread->innerThread);
        //@ open post_();
    }
    //@ close [frac]lock(lock, level, inv);
    //@ close lock_thread(thread);
    //@ is_ancestor_of_refl(p);
}

void release(struct lock_thread *thread)
    //@ requires locked(thread, ?lock, ?lockLevel, ?inv, ?frac, ?ob) &*& inv() &*& obs(?p, ?obs) &*& mem(ob, obs) == true;
    //@ ensures obs(?p1, remove(ob, obs)) &*& lock_thread(thread) &*& [frac]lock(lock, lockLevel, inv) &*& is_ancestor_of(p, p1) == true;
    //@ terminates;
{
    {
        /*@
        predicate pre() = inv();
        predicate post(list<pathcomp> p1) = is_ancestor_of(p, p1) == true;
        @*/
        /*@
        produce_lemma_function_pointer_chunk release_ghost_op(currentThread, inv, p, remove(ob, obs), pre, post)() { assert obs(?p1, _); open pre(); close post(p1); };
        @*/
        //@ close pre();
        release_with_ghost_op(thread);
        //@ open post(?p1);
        //@ assert obs(?p2, _);
        //@ is_ancestor_of_trans(p, p1, p2);
    }
}

void dispose_lock_thead(struct lock_thread *thread)
    //@ requires lock_thread(thread);
    //@ ensures true;
    //@ terminates;
{
    //@ open lock_thread(thread);
    dispose_clhlock_as_ticketlock_thread(thread->innerThread);
    free(thread);
}

void dispose_lock(struct lock *lock)
    //@ requires lock(lock, ?level, ?inv);
    //@ ensures inv();
    //@ terminates;
{
    //@ open lock(lock, level, inv);
    dispose_clhlock_as_ticketlock(lock->innerLock);
    //@ open lock_inv(lock, level, inv, lock->growingListId, lock->incrBoxId)(?owner, ?nextTicket, false);
    //@ leak incr_box(_, _) &*& growing_list(_, _);
    free(lock);
}
