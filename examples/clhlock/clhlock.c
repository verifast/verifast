//@ #include "ghost_lists.gh"

#include <stdlib.h>
#include "atomics.h"
#include "clhlock.h"

struct node {
    int lock;
    //@ struct node *pred;
    //@ real frac;
};

struct lock {
    struct node *tail;
    //@ int ghostListId;
    //@ predicate() inv_;
};

struct lock_thread {
    struct node *node;
    struct node *pred;
};

/*@

predicate queue(
    struct lock *l, predicate() inv, int ghostListId,
    struct node *n, list<struct node *> ns) =
    n == 0 ?
        ns == nil
    :
        [1/2]n->lock |-> ?lock &*&
        lock == 0 ?
            [1/2]n->lock |-> 0 &*&
            n->pred |-> _ &*&
            n->frac |-> _ &*&
            inv() &*&
            ns == {n} &*&
            ghost_list_member_handle(ghostListId, n) &*&
            malloc_block_node(n)
        :
            [1/2]n->pred |-> ?pred &*&
            [1/2]n->frac |-> ?frac &*& [frac/4]l->ghostListId |-> _ &*&
            queue(l, inv, ghostListId, pred, ?ns0) &*&
            ns == cons(n, ns0);

predicate_ctor lock_inv(struct lock *lock, predicate() inv)() =
    [1/2]lock->ghostListId |-> ?listId &*&
    lock->tail |-> ?tail &*&
    queue(lock, inv, listId, tail, cons(tail, ?ns)) &*&
    ghost_list(listId, cons(tail, ns));

predicate lock(struct lock *lock; predicate() inv) =
    lock->inv_ |-> inv &*&
    atomic_space(lock_inv(lock, inv)) &*&
    [1/2]lock->ghostListId |-> _ &*&
    malloc_block_lock(lock);

predicate lock_thread(struct lock_thread *thread) =
    thread->node |-> ?node &*& node != 0 &*& node->lock |-> _ &*& node->pred |-> _ &*& node->frac |-> _ &*& malloc_block_node(node) &*&
    thread->pred |-> _ &*&
    malloc_block_lock_thread(thread);

predicate locked(struct lock_thread *thread, struct lock *lock, predicate() inv, real frac) =
    thread->node |-> ?node &*& [1/2]node->lock |-> 1 &*& [1/2]node->pred |-> 0 &*& [1/2]node->frac |-> frac &*& malloc_block_node(node) &*&
    thread->pred |-> ?pred &*&
    malloc_block_lock_thread(thread) &*&
    pred->lock |-> _ &*& pred->pred |-> _ &*& pred->frac |-> _ &*& malloc_block_node(pred) &*& pred != 0 &*&
    [frac]lock->inv_ |-> inv &*&
    [frac]atomic_space(lock_inv(lock, inv)) &*&
    [frac]malloc_block_lock(lock) &*&
    [frac/4]lock->ghostListId |-> ?listId &*&
    ghost_list_member_handle(listId, node);

@*/

struct lock *create_lock()
    //@ requires exists<predicate()>(?inv) &*& inv();
    //@ ensures lock(result, inv);
{
    //@ open exists(_);
    struct lock *lock = malloc(sizeof(struct lock));
    if (lock == 0) abort();
    struct node *sentinel = malloc(sizeof(struct node));
    if (sentinel == 0) abort();
    sentinel->lock = 0;
    //@ sentinel->pred = 0;
    lock->tail = sentinel;
    return lock;
    //@ int ghostListId = create_ghost_list();
    //@ lock->ghostListId = ghostListId;
    //@ lock->inv_ = inv;
    //@ ghost_list_insert(ghostListId, nil, nil, sentinel);
    //@ close queue(lock, inv, ghostListId, sentinel, {sentinel});
    //@ close lock_inv(lock, inv)();
    //@ create_atomic_space(lock_inv(lock, inv));
    //@ close lock(lock, inv);
}

struct lock_thread *create_lock_thread()
    //@ requires true;
    //@ ensures lock_thread(result);
{
    struct lock_thread *thread = malloc(sizeof(struct lock_thread));
    if (thread == 0) abort();
    struct node *node = malloc(sizeof(struct node));
    if (node == 0) abort();
    thread->node = node;
    return thread;
    //@ close lock_thread(thread);
}

void acquire(struct lock_thread *thread, struct lock *lock)
    //@ requires lock_thread(thread) &*& [?frac]lock(lock, ?inv);
    //@ ensures locked(thread, lock, inv, frac) &*& inv();
{
    //@ open lock_thread(thread);
    //@ open lock(lock, inv);
    //@ int ghostListId = lock->ghostListId;
    struct node *node = thread->node;
    node->lock = 1;
    //@ node->frac = frac;
    struct node *pred;
    {
        /*@
        predicate pre() = [1/2]node->lock |-> 1 &*& node->pred |-> _ &*& [1/2]node->frac |-> frac &*& [frac/2]lock->ghostListId |-> ghostListId;
        predicate post(void *result) = ghost_list_member_handle(ghostListId, node) &*& [1/2]node->pred |-> result &*& result != 0 &*& [frac/4]lock->ghostListId |-> ghostListId;
        lemma void ghop()
            requires lock_inv(lock, inv)() &*& is_atomic_exchange_pointer_op(?op, &lock->tail, node, ?P, ?Q) &*& P() &*& pre();
            ensures lock_inv(lock, inv)() &*& is_atomic_exchange_pointer_op(op, &lock->tail, node, P, Q) &*& Q(?old) &*& post(old);
        {
            open lock_inv(lock, inv)();
            open pre();
            void *old = lock->tail;
            op();
            assert ghost_list(ghostListId, ?ns);
            open queue(lock, inv, ghostListId, old, ns);
            close queue(lock, inv, ghostListId, old, ns);
            ghost_list_insert(ghostListId, nil, ns, node);
            node->pred = old;
            close queue(lock, inv, ghostListId, node, cons(node, ns));
            close post(old);
            close lock_inv(lock, inv)();
        }
        @*/
        //@ close pre();
        //@ produce_lemma_function_pointer_chunk(ghop) : atomic_exchange_pointer_ghost_op(lock_inv(lock, inv), &lock->tail, node, pre, post)() { call(); };
        pred = atomic_exchange_pointer(&lock->tail, node);
        //@ leak is_atomic_exchange_pointer_ghost_op(ghop, _, _, _, _, _);
        //@ open post(pred);
    }
    for (;;)
         /*@
         invariant
             [frac]atomic_space(lock_inv(lock, inv)) &*&
             [frac/4]lock->ghostListId |-> ghostListId &*&
             ghost_list_member_handle(ghostListId, node) &*&
             [1/2]node->pred |-> pred;
         @*/
    {
         int predLock;
         {
             /*@
             predicate pre() =
                 [frac/4]lock->ghostListId |-> ghostListId &*&
                 ghost_list_member_handle(ghostListId, node) &*&
                 [1/2]node->pred |-> pred;
             predicate post(int value) =
                 [frac/4]lock->ghostListId |-> ghostListId &*&
                 ghost_list_member_handle(ghostListId, node) &*&
                 value == 0 ?
                     [1/2]node->pred |-> 0 &*&
                     pred->lock |-> _ &*& pred->pred |-> _ &*& pred->frac |-> _ &*& malloc_block_node(pred) &*&
                     inv()
                 :
                     [1/2]node->pred |-> pred;
             lemma void ghop()
                 requires lock_inv(lock, inv)() &*& is_atomic_load_int_op(?op, &pred->lock, ?P, ?Q) &*& P() &*& pre();
                 ensures lock_inv(lock, inv)() &*& is_atomic_load_int_op(op, &pred->lock, P, Q) &*& Q(?value) &*& post(value);
             {
                 open lock_inv(lock, inv)();
                 open pre();
                 struct node *tail = lock->tail;
                 ghost_list_member_handle_lemma();
                 {
                     lemma void iter(struct node *n, list<struct node *> ns0)
                         requires
                             queue(lock, inv, ghostListId, n, ?ns1) &*&
                             ghost_list(ghostListId, ?ns) &*& ns == cons(tail, _) &*&
                             ns == append(ns0, ns1) &*&
                             mem(node, ns1) == true &*&
                             is_atomic_load_int_op(op, &pred->lock, P, Q) &*&
                             P() &*&
                             [1/2]node->pred |-> pred;
                         ensures
                             queue(lock, inv, ghostListId, n, ?ns1_) &*&
                             ghost_list(ghostListId, ?ns_) &*& ns_ == cons(tail, _) &*&
                             ns_ == append(ns0, ns1_) &*&
                             is_atomic_load_int_op(op, &pred->lock, P, Q) &*&
                             Q(?predLock_) &*&
                             predLock_ == 0 ?
                                 [1/2]node->pred |-> 0 &*&
                                 pred->lock |-> _ &*& pred->pred |-> _ &*& pred->frac |-> _ &*& malloc_block_node(pred) &*&
                                 inv()
                             :
                                 [1/2]node->pred |-> pred;
                     {
                         open queue(lock, inv, ghostListId, n, ns1);
                         if (n == node) {
                             merge_fractions node_pred(n, _);
                             open queue(lock, inv, ghostListId, pred, ?ns1t);
                             open node_lock(pred, _);
                             op();
                             int predLock_ = pred->lock;
                             if (predLock_ == 0) {
                                 node->pred = 0;
                                 append_assoc(ns0, {n}, {pred});
                                 ghost_list_remove(ghostListId, append(ns0, {n}), nil, pred);
                                 close queue(lock, inv, ghostListId, 0, nil);
                                 close queue(lock, inv, ghostListId, n, {n});
                             } else {
                                 close queue(lock, inv, ghostListId, pred, ns1t);
                                 close queue(lock, inv, ghostListId, n, ns1);
                             }
                         } else {
                             append_assoc(ns0, {n}, tail(ns1));
                             iter(n->pred, append(ns0, {n}));
                             assert queue(lock, inv, ghostListId, _, ?ns1_);
                             append_assoc(ns0, {n}, ns1_);
                             close queue(lock, inv, ghostListId, n, cons(n, ns1_));
                         }
                     }
                     iter(lock->tail, nil);
                 }
                 assert Q(?predLock_);
                 close post(predLock_);
                 close lock_inv(lock, inv)();
             }
             @*/
             //@ close pre();
             //@ produce_lemma_function_pointer_chunk(ghop) : atomic_load_int_ghost_op(lock_inv(lock, inv), &pred->lock, pre, post)() { call(); };
             predLock = atomic_load_int(&pred->lock);
             //@ leak is_atomic_load_int_ghost_op(ghop, _, _, _, _);
             //@ open post(predLock);
         }
         if (predLock == 0) break;
    }
    thread->pred = pred;
    //@ close locked(thread, lock, inv, frac);
}

void release(struct lock_thread *thread)
    //@ requires locked(thread, ?lock, ?inv, ?frac) &*& inv();
    //@ ensures lock_thread(thread) &*& [frac]lock(lock, inv);
{
    //@ open locked(thread, lock, inv, frac);
    struct node *node = thread->node;
    //@ int ghostListId = lock->ghostListId;
    {
        /*@
        predicate pre() =
            [frac/4]lock->ghostListId |-> ghostListId &*&
            ghost_list_member_handle(ghostListId, node) &*&
            [1/2]node->lock |-> 1 &*&
            [1/2]node->pred |-> 0 &*&
            [1/2]node->frac |-> frac &*&
            malloc_block_node(node) &*&
            inv();
        predicate post() =
            [frac/2]lock->ghostListId |-> ghostListId;
        lemma void ghop()
            requires lock_inv(lock, inv)() &*& is_atomic_store_int_op(?op, &node->lock, 0, ?P, ?Q) &*& P() &*& pre();
            ensures lock_inv(lock, inv)() &*& is_atomic_store_int_op(op, &node->lock, 0, P, Q) &*& Q() &*& post();
        {
            open lock_inv(lock, inv)();
            open pre();
            ghost_list_member_handle_lemma();
            {
                lemma void iter()
                    requires
                        queue(lock, inv, ghostListId, ?n, ?ns) &*& mem(node, ns) == true &*&
                        ghost_list_member_handle(ghostListId, node) &*&
                        [1/2]node->lock |-> 1 &*&
                        [1/2]node->pred |-> 0 &*&
                        [1/2]node->frac |-> frac &*&
                        malloc_block_node(node) &*&
                        inv() &*&
                        is_atomic_store_int_op(op, &node->lock, 0, P, Q) &*& P();
                    ensures
                        queue(lock, inv, ghostListId, n, ns) &*&
                        is_atomic_store_int_op(op, &node->lock, 0, P, Q) &*& Q() &*&
                        [frac/4]lock->ghostListId |-> _;
                {
                    open queue(lock, inv, ghostListId, n, ns);
                    if (n == node) {
                        merge_fractions node_lock(n, _);
                        merge_fractions node_pred(n, _);
                        merge_fractions node_frac(n, _);
                        open queue(lock, inv, ghostListId, 0, _);
                        op();
                    } else {
                        iter();
                    }
                    close queue(lock, inv, ghostListId, n, ns);
                }
                iter();
            }
            close lock_inv(lock, inv)();
            close post();
        }
        @*/
        //@ close pre();
        //@ produce_lemma_function_pointer_chunk(ghop) : atomic_store_int_ghost_op(lock_inv(lock, inv), &node->lock, 0, pre, post)() { call(); };
        atomic_store_int(&node->lock, 0);
        //@ leak is_atomic_store_int_ghost_op(ghop, _, _, _, _, _);
        //@ open post();
    }
    thread->node = thread->pred;
    //@ close [frac]lock(lock, inv);
    //@ close lock_thread(thread);
}

void dispose_lock_thead(struct lock_thread *thread)
    //@ requires lock_thread(thread);
    //@ ensures true;
{
    //@ open lock_thread(thread);
    free(thread->node);
    free(thread);
}

void dispose_lock(struct lock *lock)
    //@ requires lock(lock, ?inv);
    //@ ensures inv();
{
    //@ open lock(lock, inv);
    //@ destroy_atomic_space();
    //@ open lock_inv(lock, inv)();
    //@ open queue(lock, inv, _, _, _);
    free(lock->tail);
    free(lock);
    //@ leak ghost_list(_, _) &*& ghost_list_member_handle(_, _);
}