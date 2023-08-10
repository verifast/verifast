// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#include <stdlib.h>
#include "atomics.h"
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

@*/

struct node {
    int lock;
    //@ unit heldToken;
    //@ real frac;
};

struct clhlock_as_ticketlock {
    struct node *tail;
    //@ predicate(int, int, bool) inv_;
    //@ box growingListId;
    //@ option<int> owner;
};

struct clhlock_as_ticketlock_thread {
    struct node *node;
    struct node *pred;
};

/*@

predicate nodes(struct clhlock_as_ticketlock *lock, list<int> nodeIds, int owner) =
    switch (nodeIds) {
        case nil: return true;
        case cons(nodeId, nodeIds0): return
            [1/3]ghost_cell<struct node *>(nodeId, ?node) &*&
            nodes(lock, nodeIds0, owner - 1) &*&
            owner > 1 ?
                node == 0
            :
                malloc_block_node(node) &*&
                owner == 1 ?
                    node->lock |-> 0 &*& [1/3]ghost_cell<struct node *>(nodeId, node) &*& node->heldToken |-> _ &*& node->frac |-> _
                :
                    node->lock |-> 1 &*& [1/2]node->frac |-> ?frac &*& [frac/2]lock->growingListId |-> _
            ;
    };

predicate_ctor clhlock_as_ticketlock_inv(struct clhlock_as_ticketlock *lock, predicate(int, int, bool) inv, box growingListId)() =
    growing_list(growingListId, ?nodeIds) &*& 1 <= length(nodeIds) &*&
    [1/2]lock->owner |-> ?ownerInfo &*&
    lock->tail |-> ?tail &*& tail != 0 &*&
    [1/3]ghost_cell(nth(length(nodeIds) - 1, nodeIds), tail) &*&
    inv(?owner, length(nodeIds) - 1, ownerInfo != none) &*& 0 <= owner &*& owner < length(nodeIds) &*&
    nodes(lock, nodeIds, owner + 1) &*&
    switch (ownerInfo) {
        case none: return [1/2]lock->owner |-> none;
        case some(o): return o == owner &*& owner + 1 < length(nodeIds) &*& [1/6]ghost_cell<struct node *>(nth(owner + 1, nodeIds), ?node) &*& node->heldToken |-> _;
    };

predicate clhlock_as_ticketlock(struct clhlock_as_ticketlock *lock; predicate(int, int, bool) inv) =
    malloc_block_clhlock_as_ticketlock(lock) &*&
    lock->inv_ |-> inv &*&
    lock->growingListId |-> ?growingListId &*&
    atomic_space(clhlock_as_ticketlock_inv(lock, inv, growingListId));

predicate clhlock_as_ticketlock_thread(struct clhlock_as_ticketlock_thread *thread) =
    thread->pred |-> _ &*&
    thread->node |-> ?node &*& node != 0 &*& node->lock |-> _ &*& node->heldToken |-> _ &*& node->frac |-> _ &*& malloc_block_node(node) &*&
    malloc_block_clhlock_as_ticketlock_thread(thread);

predicate clhlock_as_ticketlock_locked(struct clhlock_as_ticketlock_thread *thread, struct clhlock_as_ticketlock *lock, predicate(int, int, bool) inv, real frac, int ticket) =
    [frac]lock->inv_ |-> inv &*&
    [1/2]lock->owner |-> some(ticket) &*&
    [frac/2]lock->growingListId |-> ?growingListId &*&
    [frac]atomic_space(clhlock_as_ticketlock_inv(lock, inv, growingListId)) &*&
    [frac]malloc_block_clhlock_as_ticketlock(lock) &*&
    0 <= ticket &*&
    malloc_block_clhlock_as_ticketlock_thread(thread) &*&
    exists(pair(?predHandleId, ?nodeHandleId)) &*&
    thread->pred |-> ?pred &*& pred != 0 &*& has_at(predHandleId, growingListId, ticket, ?predCellId) &*& [1/3]ghost_cell(predCellId, pred) &*&
    thread->node |-> ?node &*& node != 0 &*& has_at(nodeHandleId, growingListId, ticket + 1, ?nodeCellId) &*& [1/6]ghost_cell(nodeCellId, node) &*&
    [1/2]node->frac |-> frac;

@*/

struct clhlock_as_ticketlock *create_clhlock_as_ticketlock()
//@ requires exists<predicate(int, int, bool)>(?inv) &*& inv(0, 0, false);
//@ ensures clhlock_as_ticketlock(result, inv);
//@ terminates;
{
    //@ open exists(_);
    struct clhlock_as_ticketlock *lock = malloc(sizeof(struct clhlock_as_ticketlock));
    if (lock == 0) abort();
    struct node *sentinel = malloc(sizeof(struct node));
    if (sentinel == 0) abort();
    sentinel->lock = 0;
    lock->tail = sentinel;
    //@ lock->owner = none;
    //@ int sentinelCellId = create_ghost_cell(sentinel);
    //@ close nodes(lock, {}, 0);
    //@ close nodes(lock, {sentinelCellId}, 1);
    //@ create_box growingListId = growing_list({sentinelCellId});
    //@ close clhlock_as_ticketlock_inv(lock, inv, growingListId)();
    //@ lock->inv_ = inv;
    //@ lock->growingListId = growingListId;
    //@ create_atomic_space(clhlock_as_ticketlock_inv(lock, inv, growingListId));
    return lock;
}

struct clhlock_as_ticketlock_thread *create_clhlock_as_ticketlock_thread()
//@ requires true;
//@ ensures clhlock_as_ticketlock_thread(result);
//@ terminates;
{
    struct clhlock_as_ticketlock_thread *thread = malloc(sizeof(struct clhlock_as_ticketlock_thread));
    if (thread == 0) abort();
    struct node *node = malloc(sizeof(struct node));
    if (node == 0) abort();
    thread->node = node;
    return thread;
    //@ close clhlock_as_ticketlock_thread(thread);
}

void acquire_helper(struct clhlock_as_ticketlock_thread *thread, struct clhlock_as_ticketlock *lock, struct node *pred)
    /*@
    requires
        [?frac]lock->inv_ |-> ?inv &*&
        [frac/2]lock->growingListId |-> ?growingListId &*&
        [frac]atomic_space(clhlock_as_ticketlock_inv(lock, inv, growingListId)) &*&
        [frac]malloc_block_clhlock_as_ticketlock(lock) &*&
        is_clhlock_as_ticketlock_wait_ghost_op(?wait, inv, ?wait_inv, currentThread) &*& wait_inv(?ticket, acquire_helper) &*&
        is_clhlock_as_ticketlock_acquire_ghost_op(?acq, inv, wait_inv, ?post, currentThread) &*&
        0 <= ticket &*&
        exists(pair(?predHandleId, ?nodeHandleId)) &*&
        thread->pred |-> _ &*& pred != 0 &*& has_at(predHandleId, growingListId, ticket, ?predCellId) &*& [1/3]ghost_cell(predCellId, pred) &*&
        thread->node |-> ?node &*& node != 0 &*& has_at(nodeHandleId, growingListId, ticket + 1, ?nodeCellId) &*& [1/3]ghost_cell(nodeCellId, node) &*&
        malloc_block_clhlock_as_ticketlock_thread(thread) &*&
        node->heldToken |-> _ &*& [1/2]node->frac |-> frac;
    @*/
    //@ ensures clhlock_as_ticketlock_locked(thread, lock, inv, frac, ticket) &*& post(ticket);
    //@ terminates;
{
    //@ int acquireThread = currentThread;
    for (;;)
         /*@
         invariant
             node->heldToken |-> _ &*&
             is_clhlock_as_ticketlock_wait_ghost_op(wait, inv, wait_inv, currentThread) &*& wait_inv(ticket, acquire_helper) &*&
             is_clhlock_as_ticketlock_acquire_ghost_op(acq, inv, wait_inv, post, currentThread) &*&
             [frac]atomic_space(clhlock_as_ticketlock_inv(lock, inv, growingListId)) &*&
             has_at(predHandleId, growingListId, ticket, predCellId) &*& [1/3]ghost_cell(predCellId, pred) &*&
             thread->node |-> node &*& has_at(nodeHandleId, growingListId, ticket + 1, nodeCellId) &*& [1/3]ghost_cell(nodeCellId, node);
         @*/
    {
         int predLock;
         {
             /*@
             predicate pre_() =
                 is_clhlock_as_ticketlock_wait_ghost_op(wait, inv, wait_inv, currentThread) &*& wait_inv(ticket, acquire_helper) &*&
                 is_clhlock_as_ticketlock_acquire_ghost_op(acq, inv, wait_inv, post, currentThread) &*&
                 has_at(predHandleId, growingListId, ticket, predCellId) &*& [1/3]ghost_cell(predCellId, pred) &*&
                 has_at(nodeHandleId, growingListId, ticket + 1, nodeCellId) &*& [1/3]ghost_cell(nodeCellId, node) &*&
                 node->heldToken |-> _
                 ;
             predicate post_(int value) =
                 has_at(predHandleId, growingListId, ticket, predCellId) &*& [1/3]ghost_cell(predCellId, pred) &*&
                 has_at(nodeHandleId, growingListId, ticket + 1, nodeCellId) &*& [1/6]ghost_cell(nodeCellId, node) &*&
                 value == 0 ?
                     [1/2]lock->owner |-> some(ticket) &*&
                     post(ticket)
                 :
                     [1/6]ghost_cell(nodeCellId, node) &*&
                     node->heldToken |-> _ &*&
                     is_clhlock_as_ticketlock_wait_ghost_op(wait, inv, wait_inv, currentThread) &*& wait_inv(ticket, acquire_helper) &*&
                     is_clhlock_as_ticketlock_acquire_ghost_op(acq, inv, wait_inv, post, currentThread) &*&
                     call_perm_(currentThread, acquire_helper)
                     ;
             @*/
             /*@
             produce_lemma_function_pointer_chunk atomic_load_int_ghost_op(clhlock_as_ticketlock_inv(lock, inv, growingListId), &pred->lock, currentThread, pre_, post_)() {
                 open clhlock_as_ticketlock_inv(lock, inv, growingListId)();
                 open pre_();
                 consuming_box_predicate growing_list(growingListId, ?nodeIds)
                 consuming_handle_predicate has_at(predHandleId, ticket, predCellId)
                 consuming_handle_predicate has_at(nodeHandleId, ticket + 1, nodeCellId)
                 perform_action noop() {}
                 producing_box_predicate growing_list(nodeIds)
                 producing_handle_predicate has_at(predHandleId, ticket, predCellId)
                 producing_handle_predicate has_at(nodeHandleId, ticket + 1, nodeCellId);
                 assert is_atomic_load_int_op(?op, &pred->lock, ?P, ?Q);
                 assert inv(?owner, ?nextTicket, ?held);
                 int ticketOffset = ticket - owner;
                 {
                     lemma void iter()
                         requires
                             nodes(lock, ?nodeIds0, ?owner0) &*& 0 <= owner0 + ticketOffset - 1 &*& owner0 + ticketOffset < length(nodeIds0) &*&
                             is_atomic_load_int_op(op, &pred->lock, P, Q) &*& P() &*&
                             nth(owner0 + ticketOffset - 1, nodeIds0) == predCellId &*& [1/3]ghost_cell(predCellId, pred) &*&
                             nth(owner0 + ticketOffset, nodeIds0) == nodeCellId &*& [1/3]ghost_cell(nodeCellId, node);
                         ensures
                             is_atomic_load_int_op(op, &pred->lock, P, Q) &*& Q(?value) &*&
                             nodes(lock, nodeIds0, owner0) &*&
                             [1/3]ghost_cell(predCellId, pred) &*&
                             [1/3]ghost_cell(nodeCellId, node) &*&
                             value == 0 ?
                                 ticketOffset == 0
                             :
                                 0 < ticketOffset;
                     {
                         open nodes(lock, nodeIds0, owner0);
                         if (0 < owner0 + ticketOffset - 1) {
                             iter();
                         } else {
                             assert owner0 + ticketOffset - 1 == 0;
                             merge_fractions ghost_cell(predCellId, _);
                             op();
                         }
                         close nodes(lock, nodeIds0, owner0);
                     }
                     iter();
                 }
                 assert Q(?value);
                 if (value == 0) {
                     switch (lock->owner) {
                         case none:
                         case some(o):
                             assert o == owner;
                             merge_fractions ghost_cell(nodeCellId, _);
                             assert false;
                     }
                     acq();
                     lock->owner = some(ticket);
                     leak is_clhlock_as_ticketlock_wait_ghost_op(_, _, _, _);
                     leak is_clhlock_as_ticketlock_acquire_ghost_op(_, _, _, _, _);
                 } else {
                     wait();
                 }
                 close clhlock_as_ticketlock_inv(lock, inv, growingListId)();
                 close post_(value);
             };
             @*/
             //@ close pre_();
             predLock = atomic_load_int(&pred->lock);
             //@ leak is_atomic_load_int_ghost_op(_, _, _, _, _, _);
             //@ open post_(predLock);
         }
         if (predLock == 0) break;
    }
    thread->pred = pred;
    //@ close clhlock_as_ticketlock_locked(thread, lock, inv, frac, ticket);
}

void clhlock_as_ticketlock_acquire(struct clhlock_as_ticketlock_thread *thread, struct clhlock_as_ticketlock *lock)
    /*@
    requires
        clhlock_as_ticketlock_thread(thread) &*& [?frac]clhlock_as_ticketlock(lock, ?inv) &*&
        is_clhlock_as_ticketlock_get_ticket_ghost_op(?getTicket, inv, ?pre, ?wait_inv, currentThread) &*&
        is_clhlock_as_ticketlock_wait_ghost_op(?wait, inv, wait_inv, currentThread) &*&
        is_clhlock_as_ticketlock_acquire_ghost_op(?acq, inv, wait_inv, ?post, currentThread) &*&
        pre();
    @*/
    //@ ensures clhlock_as_ticketlock_locked(thread, lock, inv, frac, ?ticket) &*& post(ticket);
    //@ terminates;
{
    //@ open clhlock_as_ticketlock_thread(thread);
    //@ open clhlock_as_ticketlock(lock, inv);
    //@ box growingListId = lock->growingListId;
    struct node *node = thread->node;
    //@ int nodeCellId = create_ghost_cell(node);
    node->lock = 1;
    //@ node->frac = frac;
    struct node *pred;
    {
        /*@
        predicate pre_() =
            is_clhlock_as_ticketlock_get_ticket_ghost_op(getTicket, inv, pre, wait_inv, currentThread) &*&
            node->lock |-> 1 &*& malloc_block_node(node) &*& [1/2]node->frac |-> frac &*& [frac/2]lock->growingListId |-> _ &*&
            ghost_cell(nodeCellId, node) &*&
            pre();
        predicate post_(void *result) =
            wait_inv(?ticket, acquire_helper) &*&
            0 <= ticket &*&
            result != 0 &*&
            exists(pair(?predHandleId, ?nodeHandleId)) &*&
            has_at(predHandleId, growingListId, ticket, ?predCellId) &*& [1/3]ghost_cell(predCellId, result) &*&
            has_at(nodeHandleId, growingListId, ticket + 1, nodeCellId) &*& [1/3]ghost_cell(nodeCellId, node);
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_exchange_pointer_ghost_op(clhlock_as_ticketlock_inv(lock, inv, growingListId), &lock->tail, node, pre_, post_, currentThread)() {
            open clhlock_as_ticketlock_inv(lock, inv, growingListId)();
            open pre_();
            assert inv(?owner, ?nextTicket, ?held);
            assert is_atomic_exchange_pointer_op(?op, &lock->tail, node, ?P, ?Q);
            struct node *pred_ = lock->tail;
            consuming_box_predicate growing_list(growingListId, ?nodeIds)
            perform_action noop() {}
            producing_fresh_handle_predicate has_at(length(nodeIds) - 1, nth(length(nodeIds) - 1, nodeIds));
            assert has_at(?predHandleId, growingListId, length(nodeIds) - 1, ?predCellId);
            consuming_box_predicate growing_list(growingListId, nodeIds)
            perform_action add(nodeCellId) {
                nth_append(nodeIds, {nodeCellId}, length(nodeIds) - 1);
                nth_append_r(nodeIds, {nodeCellId}, 0);
            }
            producing_box_predicate growing_list(append(nodeIds, {nodeCellId}))
            producing_fresh_handle_predicate has_at(length(nodeIds), nodeCellId);
            assert has_at(predHandleId, _, _, _) &*& has_at(?nodeHandleId, growingListId, length(nodeIds), nodeCellId);
            op();
            getTicket(acquire_helper);
            leak is_clhlock_as_ticketlock_get_ticket_ghost_op(getTicket, _, _, _, _);
            {
                lemma void iter()
                    requires
                        nodes(lock, ?nodeIds0, ?owner0) &*& owner0 <= length(nodeIds0) &*&
                        [1/3]ghost_cell(nodeCellId, node) &*& node->lock |-> 1 &*&
                        [1/2]node->frac |-> frac &*& [frac/2]lock->growingListId |-> _ &*&
                        malloc_block_node(node);
                    ensures nodes(lock, append(nodeIds0, {nodeCellId}), owner0);
                {
                    open nodes(lock, nodeIds0, owner0);
                    if (nodeIds0 == nil) {
                        close nodes(lock, nil, owner0 - 1);
                    } else {
                        iter();
                    }
                    close nodes(lock, append(nodeIds0, {nodeCellId}), owner0);
                }
                iter();
            }
            close exists(pair(predHandleId, nodeHandleId));
            close post_(pred_);
            switch (lock->owner) {
                case none:
                case some(o):
                    nth_append(nodeIds, {nodeCellId}, owner + 1);
            }
            close clhlock_as_ticketlock_inv(lock, inv, growingListId)();
        };
        @*/
        //@ close pre_();
        pred = atomic_exchange_pointer(&lock->tail, node);
        //@ leak is_atomic_exchange_pointer_ghost_op(_, _, _, _, _, _, _);
        //@ open post_(pred);
    }
    acquire_helper(thread, lock, pred);
}

void clhlock_as_ticketlock_release(struct clhlock_as_ticketlock_thread *thread)
    /*@
    requires
        clhlock_as_ticketlock_locked(thread, ?lock, ?inv, ?frac, ?ticket) &*&
        is_clhlock_as_ticketlock_release_ghost_op(?rel, inv, ticket, ?pre, ?post, currentThread) &*& pre();
    @*/
    //@ ensures clhlock_as_ticketlock_thread(thread) &*& [frac]clhlock_as_ticketlock(lock, inv) &*& post();
    //@ terminates;
{
    //@ int releaseThread = currentThread;
    //@ open clhlock_as_ticketlock_locked(thread, lock, inv, frac, ticket);
    //@ open exists(pair(?predHandleId, ?nodeHandleId));
    //@ struct node *pred = thread->pred;
    struct node *node = thread->node;
    //@ box growingListId = lock->growingListId;
    {
        /*@
        predicate pre_() =
            [1/2]lock->owner |-> some(ticket) &*& [1/2]node->frac |-> frac &*&
            is_clhlock_as_ticketlock_release_ghost_op(rel, inv, ticket, pre, post, releaseThread) &*& pre() &*&
            has_at(predHandleId, growingListId, ticket, ?predCellId) &*& [1/3]ghost_cell<struct node *>(predCellId, pred) &*&
            has_at(nodeHandleId, growingListId, ticket + 1, ?nodeCellId) &*& [1/6]ghost_cell(nodeCellId, node);
        predicate post_() =
            malloc_block_node(pred) &*& pred->lock |-> 0 &*& pred->heldToken |-> _ &*& pred->frac |-> _ &*& [frac/2]lock->growingListId |-> _ &*&
            post();
        @*/
        //@ close pre_();
        /*@
        produce_lemma_function_pointer_chunk atomic_store_int_ghost_op(clhlock_as_ticketlock_inv(lock, inv, growingListId), &node->lock, 0, pre_, post_, currentThread)() {
            open clhlock_as_ticketlock_inv(lock, inv, growingListId)();
            open pre_();
            consuming_box_predicate growing_list(growingListId, ?nodeIds)
            consuming_handle_predicate has_at(predHandleId, ticket, ?predCellId)
            consuming_handle_predicate has_at(nodeHandleId, ticket + 1, ?nodeCellId)
            perform_action noop() {};
            merge_fractions ghost_cell(nodeCellId, _);
            assert is_atomic_store_int_op(?op, &node->lock, 0, ?P, ?Q);
            {
                lemma void iter()
                    requires
                        nodes(lock, ?nodeIds0, ?owner0) &*& 1 <= owner0 &*& owner0 < length(nodeIds0) &*&
                        is_atomic_store_int_op(op, &node->lock, 0, P, Q) &*& P() &*&
                        [1/3]ghost_cell<struct node *>(nth(owner0 - 1, nodeIds0), pred) &*&
                        [1/3]ghost_cell(nth(owner0, nodeIds0), node) &*& node->heldToken |-> _ &*& [1/2]node->frac |-> frac;
                    ensures nodes(lock, nodeIds0, owner0 + 1) &*&
                        is_atomic_store_int_op(op, &node->lock, 0, P, Q) &*& Q() &*& [2/3]ghost_cell<struct node *>(nth(owner0 - 1, nodeIds0), 0) &*&
                        malloc_block_node(pred) &*& pred->lock |-> 0 &*& pred->heldToken |-> _ &*& pred->frac |-> _ &*& [frac/2]lock->growingListId |-> _;
                {
                    open nodes(lock, nodeIds0, owner0);
                    if (owner0 == 1) {
                        merge_fractions ghost_cell(head(nodeIds0), _);
                        ghost_cell_mutate<struct node *>(head(nodeIds0), 0);
                        
                        open nodes(lock, tail(nodeIds0), 0);
                        op();
                        {
                            lemma void iter2()
                                requires nodes(lock, ?nodeIds1, ?owner1) &*& owner1 < 0;
                                ensures nodes(lock, nodeIds1, owner1 + 1);
                            {
                                open nodes(lock, nodeIds1, owner1);
                                if (nodeIds1 != nil)
                                    iter2();
                                close nodes(lock, nodeIds1, owner1 + 1);
                            }
                            iter2();
                        }
                        close nodes(lock, tail(nodeIds0), 1);
                    } else {
                        iter();
                    }
                    close nodes(lock, nodeIds0, owner0 + 1);
                }
                iter();
            }
            lock->owner = none;
            rel();
            leak is_clhlock_as_ticketlock_release_ghost_op(rel, inv, ticket, pre, post, currentThread);
            close post_();
            close clhlock_as_ticketlock_inv(lock, inv, growingListId)();
            leak [2/3]ghost_cell<struct node *>(predCellId, _);
        };
        @*/
        atomic_store_int(&node->lock, 0);
        //@ leak is_atomic_store_int_ghost_op(_, _, _, _, _, _, _);
        //@ open post_();
    }
    thread->node = thread->pred;
    //@ close [frac]clhlock_as_ticketlock(lock, inv);
    //@ close clhlock_as_ticketlock_thread(thread);
}

void dispose_clhlock_as_ticketlock_thread(struct clhlock_as_ticketlock_thread *thread)
    //@ requires clhlock_as_ticketlock_thread(thread);
    //@ ensures true;
    //@ terminates;

{
    //@ open clhlock_as_ticketlock_thread(thread);
    free(thread->node);
    free(thread);
}

void dispose_clhlock_as_ticketlock(struct clhlock_as_ticketlock *lock)
    //@ requires clhlock_as_ticketlock(lock, ?inv);
    //@ ensures inv(?owner, owner, false);
    //@ terminates;

{
    //@ open clhlock_as_ticketlock(lock, inv);
    //@ destroy_atomic_space();
    //@ open clhlock_as_ticketlock_inv(lock, inv, lock->growingListId)();
    //@ struct node *tail = lock->tail;
    //@ assert nodes(lock, ?nodeIds, _);
    //@ int tailCellId = nth(length(nodeIds) - 1, nodeIds);
    //@ assert [1/3]ghost_cell(tailCellId, tail);
    /*@
    {
        lemma void iter()
            requires
                nodes(lock, ?nodeIds0, ?owner0) &*&
                1 <= length(nodeIds0) &*&
                tailCellId == nth(length(nodeIds0) - 1, nodeIds0) &*&
                [1/3]ghost_cell(tailCellId, tail) &*&
                owner0 <= length(nodeIds0) &*& lock->growingListId |-> _;
            ensures length(nodeIds0) == owner0 &*& tail->lock |-> _ &*& tail->heldToken |-> _ &*& tail->frac |-> _ &*& malloc_block_node(tail) &*& lock->growingListId |-> _;
        {
            open nodes(_, _, _);
            leak [_]ghost_cell(_, _);
            if (length(nodeIds0) > 1)
                iter();
            else {
                open nodes(lock, tail(nodeIds0), owner0 - 1);
                merge_fractions ghost_cell(tailCellId, _);
            }
        }
        iter();
    }
    @*/
    free(lock->tail);
    free(lock);
    //@ leak growing_list(_, _);
}
