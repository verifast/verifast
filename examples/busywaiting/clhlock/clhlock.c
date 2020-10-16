// Tobias Reinhard and Bart Jacobs. Ghost signals: verifying termination of busy-waiting. 2020.

//@ #include "ghost_lists.gh"

#include <stdlib.h>
#include "atomics.h"
#include "clhlock.h"
//@ #include <quantifiers.gh>

struct node {
    int lock;
    //@ struct node *pred;
    //@ real frac;
    //@ void *signal;
    //@ void *predSignal;
    //@ int level;
};

struct lock {
    struct node *tail;
    //@ int ghostListId;
    //@ list<int> level;
};

struct lock_thread {
    struct node *node;
    struct node *pred;
};

/*@

predicate queue(
    struct lock *l, list<int> lockLevel, predicate() inv, int ghostListId,
    void *signal, int level,
    struct node *n, list<struct node *> ns) =
    0 <= level &*&
    n == 0 ?
        ns == nil
    :
        [1/2]n->lock |-> ?lock &*&
        lock == 0 ?
            [1/2]n->lock |-> 0 &*&
            n->pred |-> _ &*&
            n->frac |-> _ &*&
            n->level |-> _ &*&
            n->signal |-> _ &*&
            n->predSignal |-> _ &*&
            inv() &*&
            ns == {n} &*&
            ghost_list_member_handle(ghostListId, n) &*&
            malloc_block_node(n)
        :
            [1/2]n->pred |-> ?pred &*&
            [1/2]n->frac |-> ?frac &*& [frac/4]l->ghostListId |-> _ &*&
            [1/2]n->signal |-> signal &*& [1/2]n->level |-> level &*&
            [1/2]n->predSignal |-> ?predSignal &*&
            signal(signal, append(lockLevel, {level}), false) &*&
            queue(l, lockLevel, inv, ghostListId, predSignal, level - 1, pred, ?ns0) &*&
            ns == cons(n, ns0);

predicate_ctor lock_inv(struct lock *lock, predicate() inv)() =
    [1/2]lock->ghostListId |-> ?listId &*& [1/2]lock->level |-> ?lockLevel &*&
    lock->tail |-> ?tail &*&
    queue(lock, lockLevel, inv, listId, _, _, tail, cons(tail, ?ns)) &*&
    ghost_list(listId, cons(tail, ns));

predicate lock(struct lock *lock, list<int> level, predicate() inv;) =
    [1/2]lock->level |-> level &*&
    atomic_space(lock_inv(lock, inv)) &*&
    [1/2]lock->ghostListId |-> _ &*&
    malloc_block_lock(lock);

predicate lock_thread(struct lock_thread *thread) =
    thread->node |-> ?node &*& node != 0 &*& node->lock |-> _ &*& node->pred |-> _ &*& node->frac |-> _ &*& malloc_block_node(node) &*&
    node->predSignal |-> _ &*& node->signal |-> _ &*& node->level |-> _ &*&
    thread->pred |-> _ &*&
    malloc_block_lock_thread(thread);

predicate locked(struct lock_thread *thread, struct lock *lock, list<int> level, predicate() inv, real frac, pair<void *, list<int> > ob) =
    thread->node |-> ?node &*& [1/2]node->lock |-> 1 &*& [1/2]node->pred |-> 0 &*& [1/2]node->frac |-> frac &*& malloc_block_node(node) &*&
    [1/2]node->predSignal |-> _ &*& [1/2]node->signal |-> ?signal &*& [1/2]node->level |-> ?obLevel &*& ob == pair(signal, append(level, {obLevel})) &*&
    thread->pred |-> ?pred &*&
    malloc_block_lock_thread(thread) &*&
    pred->lock |-> _ &*& pred->pred |-> _ &*& pred->frac |-> _ &*& pred->predSignal |-> _ &*& pred->signal |-> _ &*& pred->level |-> _ &*& malloc_block_node(pred) &*& pred != 0 &*&
    [frac/2]lock->level |-> level &*&
    [frac]atomic_space(lock_inv(lock, inv)) &*&
    [frac]malloc_block_lock(lock) &*&
    [frac/4]lock->ghostListId |-> ?listId &*&
    ghost_list_member_handle(listId, node);

@*/

struct lock *create_lock()
    //@ requires exists<list<int> >(?lockLevel) &*& exists<predicate()>(?inv) &*& inv();
    //@ ensures lock(result, lockLevel, inv);
    //@ terminates;
{
    //@ open exists(_);
    struct lock *lock = malloc(sizeof(struct lock));
    if (lock == 0) abort();
    struct node *sentinel = malloc(sizeof(struct node));
    if (sentinel == 0) abort();
    sentinel->lock = 0;
    //@ sentinel->pred = 0;
    //@ sentinel->level = 0;
    lock->tail = sentinel;
    return lock;
    //@ int ghostListId = create_ghost_list();
    //@ lock->ghostListId = ghostListId;
    //@ lock->level = lockLevel;
    //@ ghost_list_insert(ghostListId, nil, nil, sentinel);
    //@ close queue(lock, lockLevel, inv, ghostListId, sentinel->signal, 0, sentinel, {sentinel});
    //@ close lock_inv(lock, inv)();
    //@ create_atomic_space(lock_inv(lock, inv));
    //@ close lock(lock, lockLevel, inv);
}

struct lock_thread *create_lock_thread()
    //@ requires true;
    //@ ensures lock_thread(result);
    //@ terminates;
{
    struct lock_thread *thread = malloc(sizeof(struct lock_thread));
    if (thread == 0) abort();
    struct node *node = malloc(sizeof(struct node));
    if (node == 0) abort();
    thread->node = node;
    return thread;
    //@ close lock_thread(thread);
}

/*@

lemma void is_ancestor_of_refl(list<pathcomp> p)
    requires true;
    ensures is_ancestor_of(p, p) == true;
{
    switch (p) { case nil: case cons(h, t): }
}

lemma void is_ancestor_of_trans(list<pathcomp> p1, list<pathcomp> p2, list<pathcomp> p3)
    requires is_ancestor_of(p1, p2) && is_ancestor_of(p2, p3);
    ensures is_ancestor_of(p1, p3) == true;
{
    switch (p3) {
        case nil:
        case cons(p3h, p3t):
            if (p2 == p3) {
            } else {
                is_ancestor_of_trans(p1, p2, p3t);
            }
    }
}

@*/

void acquire_helper(struct lock_thread *thread, struct lock *lock, struct node *pred)
    /*@
    requires
        thread->node |-> ?node &*& node != 0 &*& [1/2]node->lock |-> 1 &*& [1/2]node->frac |-> ?frac &*& malloc_block_node(node) &*&
        thread->pred |-> _ &*&
        [1/2]node->signal |-> ?signal &*& [1/2]node->level |-> ?level &*& [1/2]node->predSignal |-> ?predSignal &*&
        [frac/2]lock->level |-> ?lockLevel &*&
        obs(?p, cons(pair(signal, append(lockLevel, {level})), ?obs)) &*& forall(map(snd, obs), (all_sublevels_lt)(lockLevel)) == true &*&
        wait_perm(p, predSignal, append(lockLevel, {level - 1}), acquire_helper) &*&
        malloc_block_lock_thread(thread) &*&
        [frac]malloc_block_lock(lock) &*&
        exists<predicate()>(?inv) &*&
        [frac]atomic_space(lock_inv(lock, inv)) &*&
        [frac/4]lock->ghostListId |-> ?ghostListId &*&
        ghost_list_member_handle(ghostListId, node) &*&
        [1/2]node->pred |-> pred &*& pred != 0;
    @*/
    //@ ensures locked(thread, lock, lockLevel, inv, frac, ?ob) &*& inv() &*& obs(?p1, cons(ob, obs)) &*& is_ancestor_of(p, p1) == true &*& level_lt(lockLevel, level_of(ob)) == true;
    //@ terminates;
{
    //@ int acquireThread = currentThread;
    for (;;)
         /*@
         invariant
             obs(p, cons(pair(signal, append(lockLevel, {level})), obs)) &*&
             wait_perm(p, predSignal, append(lockLevel, {level - 1}), acquire_helper) &*&
             [frac]atomic_space(lock_inv(lock, inv)) &*&
             [frac/4]lock->ghostListId |-> ghostListId &*& [frac/2]lock->level |-> lockLevel &*&
             ghost_list_member_handle(ghostListId, node) &*&
             [1/2]node->pred |-> pred &*& [1/2]node->predSignal |-> predSignal &*& [1/2]node->level |-> level;
         @*/
    {
         int predLock;
         {
             /*@
             predicate pre() =
                 obs(p, cons(pair(signal, append(lockLevel, {level})), obs)) &*&
                 wait_perm(p, predSignal, append(lockLevel, {level - 1}), acquire_helper) &*&
                 [frac/4]lock->ghostListId |-> ghostListId &*& [frac/2]lock->level |-> lockLevel &*&
                 ghost_list_member_handle(ghostListId, node) &*&
                 [1/2]node->pred |-> pred &*& [1/2]node->predSignal |-> predSignal &*& [1/2]node->level |-> level;
             predicate post(int value) =
                 obs(p, cons(pair(signal, append(lockLevel, {level})), obs)) &*&
                 wait_perm(p, predSignal, append(lockLevel, {level - 1}), acquire_helper) &*&
                 [frac/4]lock->ghostListId |-> ghostListId &*& [frac/2]lock->level |-> lockLevel &*&
                 ghost_list_member_handle(ghostListId, node) &*&
                 value == 0 ?
                     [1/2]node->pred |-> 0 &*& [1/2]node->predSignal |-> _ &*& [1/2]node->level |-> level &*&
                     pred->lock |-> _ &*& pred->pred |-> _ &*& pred->frac |-> _ &*& pred->predSignal |-> _ &*& pred->signal |-> _ &*& pred->level |-> _ &*& malloc_block_node(pred) &*&
                     inv()
                 :
                     [1/2]node->pred |-> pred &*& [1/2]node->predSignal |-> predSignal &*& [1/2]node->level |-> level &*& call_perm_(currentThread, acquire_helper);
             lemma void ghop()
                 requires lock_inv(lock, inv)() &*& is_atomic_load_int_op(?op, &pred->lock, ?P, ?Q) &*& P() &*& pre() &*& currentThread == acquireThread;
                 ensures lock_inv(lock, inv)() &*& is_atomic_load_int_op(op, &pred->lock, P, Q) &*& Q(?value) &*& post(value);
             {
                 open lock_inv(lock, inv)();
                 open pre();
                 struct node *tail = lock->tail;
                 ghost_list_member_handle_lemma();
                 {
                     lemma void iter(struct node *n, list<struct node *> ns0)
                         requires
                             queue(lock, lockLevel, inv, ghostListId, ?sn, ?ln, n, ?ns1) &*&
                             obs(p, cons(pair(signal, append(lockLevel, {level})), obs)) &*&
                             wait_perm(p, predSignal, append(lockLevel, {level - 1}), acquire_helper) &*&
                             ghost_list(ghostListId, ?ns) &*& ns == cons(tail, _) &*&
                             ns == append(ns0, ns1) &*&
                             mem(node, ns1) == true &*&
                             is_atomic_load_int_op(op, &pred->lock, P, Q) &*&
                             P() &*&
                             [1/2]node->pred |-> pred &*& [1/2]node->predSignal |-> predSignal &*& [1/2]node->level |-> level;
                         ensures
                             queue(lock, lockLevel, inv, ghostListId, sn, ln, n, ?ns1_) &*&
                             obs(p, cons(pair(signal, append(lockLevel, {level})), obs)) &*&
                             wait_perm(p, predSignal, append(lockLevel, {level - 1}), acquire_helper) &*&
                             ghost_list(ghostListId, ?ns_) &*& ns_ == cons(tail, _) &*&
                             ns_ == append(ns0, ns1_) &*&
                             is_atomic_load_int_op(op, &pred->lock, P, Q) &*&
                             Q(?predLock_) &*&
                             predLock_ == 0 ?
                                 [1/2]node->pred |-> 0 &*& [1/2]node->predSignal |-> _ &*& [1/2]node->level |-> level &*&
                                 pred->lock |-> _ &*& pred->pred |-> _ &*& pred->frac |-> _ &*& pred->predSignal |-> _ &*& pred->level |-> _ &*& pred->signal |-> _ &*& malloc_block_node(pred) &*&
                                 inv()
                             :
                                 [1/2]node->pred |-> pred &*& [1/2]node->predSignal |-> predSignal &*& [1/2]node->level |-> level &*& call_perm_(currentThread, acquire_helper);
                     {
                         open queue(lock, lockLevel, inv, ghostListId, sn, ln, n, ns1);
                         if (n == node) {
                             merge_fractions node_pred(n, _);
                             merge_fractions node_predSignal(n, _);
                             merge_fractions node_level(n, _);
                             open queue(lock, lockLevel, inv, ghostListId, ?spred, ?lpred, pred, ?ns1t);
                             open node_lock(pred, _);
                             op();
                             int predLock_ = pred->lock;
                             if (predLock_ == 0) {
                                 node->pred = 0;
                                 append_assoc(ns0, {n}, {pred});
                                 ghost_list_remove(ghostListId, append(ns0, {n}), nil, pred);
                                 close queue(lock, lockLevel, inv, ghostListId, spred, ln - 1, 0, nil);
                                 close queue(lock, lockLevel, inv, ghostListId, sn, ln, n, {n});
                             } else {
                                 is_ancestor_of_refl(p);
                                 level_lt_append(lockLevel, {level - 1}, {level});
                                 if (!forall(map(snd, obs), (level_lt)(append(lockLevel, {level - 1})))) {
                                     list<int> l = not_forall(map(snd, obs), (level_lt)(append(lockLevel, {level - 1})));
                                     forall_elim(map(snd, obs), (all_sublevels_lt)(lockLevel), l);
                                     assert !level_lt(append(lockLevel, {level - 1}), l);
                                     all_sublevels_lt_append(lockLevel, {level - 1}, l);
                                     assert false;
                                 }
                                 wait(predSignal);
                                 close queue(lock, lockLevel, inv, ghostListId, spred, ln - 1, pred, ns1t);
                                 close queue(lock, lockLevel, inv, ghostListId, sn, ln, n, ns1);
                             }
                         } else {
                             append_assoc(ns0, {n}, tail(ns1));
                             iter(n->pred, append(ns0, {n}));
                             assert queue(lock, lockLevel, inv, ghostListId, _, _, _, ?ns1_);
                             append_assoc(ns0, {n}, ns1_);
                             close queue(lock, lockLevel, inv, ghostListId, sn, ln, n, cons(n, ns1_));
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
             //@ produce_lemma_function_pointer_chunk(ghop) : atomic_load_int_ghost_op(lock_inv(lock, inv), &pred->lock, currentThread, pre, post)() { call(); };
             predLock = atomic_load_int(&pred->lock);
             //@ leak is_atomic_load_int_ghost_op(ghop, _, _, _, _, _);
             //@ open post(predLock);
         }
         if (predLock == 0) break;
    }
    thread->pred = pred;
    //@ close locked(thread, lock, lockLevel, inv, frac, pair(signal, append(lockLevel, {level})));
    //@ is_ancestor_of_refl(p);
    //@ leak wait_perm(p, predSignal, append(lockLevel, {level - 1}), acquire_helper);
    //@ level_lt_append(lockLevel, {}, {level});
}

void acquire(struct lock_thread *thread, struct lock *lock)
    //@ requires obs(?p, ?obs) &*& lock_thread(thread) &*& [?frac]lock(lock, ?lockLevel, ?inv) &*& forall(map(snd, obs), (all_sublevels_lt)(lockLevel)) == true;
    //@ ensures locked(thread, lock, lockLevel, inv, frac, ?ob) &*& inv() &*& obs(?p1, cons(ob, obs)) &*& is_ancestor_of(p, p1) == true &*& level_lt(lockLevel, level_of(ob)) == true;
    //@ terminates;
{
    //@ open lock_thread(thread);
    //@ open lock(lock, lockLevel, inv);
    //@ int ghostListId = lock->ghostListId;
    struct node *node = thread->node;
    node->lock = 1;
    //@ node->frac = frac;
    struct node *pred;
    {
        /*@
        predicate pre() = obs(p, obs) &*& node->predSignal |-> _ &*& node->signal |-> _ &*& node->level |-> _ &*& [1/2]node->lock |-> 1 &*& node->pred |-> _ &*& [1/2]node->frac |-> frac &*& [frac/2]lock->level |-> lockLevel &*& [frac/2]lock->ghostListId |-> ghostListId;
        predicate post(void *result) =
            ghost_list_member_handle(ghostListId, node) &*& [1/2]node->pred |-> result &*& result != 0 &*& [frac/2]lock->level |-> lockLevel &*& [frac/4]lock->ghostListId |-> ghostListId &*&
            [1/2]node->predSignal |-> ?predSignal &*& [1/2]node->signal |-> ?signal &*& [1/2]node->level |-> ?level &*& obs(p, cons(pair(signal, append(lockLevel, {level})), obs));
        lemma void ghop()
            requires lock_inv(lock, inv)() &*& is_atomic_exchange_pointer_op(?op, &lock->tail, node, ?P, ?Q) &*& P() &*& pre();
            ensures lock_inv(lock, inv)() &*& is_atomic_exchange_pointer_op(op, &lock->tail, node, P, Q) &*& Q(?old) &*& post(old);
        {
            open lock_inv(lock, inv)();
            open pre();
            void *old = lock->tail;
            op();
            assert ghost_list(ghostListId, ?ns);
            open queue(lock, lockLevel, inv, ghostListId, ?oldSignal, ?oldLevel, old, ns);
            close queue(lock, lockLevel, inv, ghostListId, oldSignal, oldLevel, old, ns);
            ghost_list_insert(ghostListId, nil, ns, node);
            node->pred = old;
            node->signal = create_signal();
            init_signal(node->signal, append(lockLevel, {oldLevel + 1}));
            node->level = oldLevel + 1;
            node->predSignal = oldSignal;
            close queue(lock, lockLevel, inv, ghostListId, node->signal, oldLevel + 1, node, cons(node, ns));
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
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    //@ create_wait_perm(node->predSignal, append(lockLevel, {node->level - 1}), acquire_helper);
    //@ close exists(inv);
    acquire_helper(thread, lock, pred);
}

void release_with_ghost_op(struct lock_thread *thread)
    //@ requires locked(thread, ?lock, ?lockLevel, ?inv, ?frac, ?ob) &*& obs(?p, ?obs) &*& is_release_ghost_op(?rgo, currentThread, inv, p, remove(ob, obs), ?pre, ?post) &*& pre();
    //@ ensures post(?p1) &*& obs(?p2, remove(ob, obs)) &*& lock_thread(thread) &*& [frac]lock(lock, lockLevel, inv) &*& is_ancestor_of(p1, p2) == true;
    //@ terminates;
{
    //@ int releaseThread = currentThread;
    //@ open locked(thread, lock, lockLevel, inv, frac, ob);
    struct node *node = thread->node;
    //@ int ghostListId = lock->ghostListId;
    {
        /*@
        predicate ghop_pre() =
            [frac/4]lock->ghostListId |-> ghostListId &*& [frac/2]lock->level |-> lockLevel &*&
            ghost_list_member_handle(ghostListId, node) &*&
            [1/2]node->lock |-> 1 &*&
            [1/2]node->pred |-> 0 &*&
            [1/2]node->frac |-> frac &*&
            [1/2]node->signal |-> ?signal &*&
            [1/2]node->level |-> ?level &*& ob == pair(signal, append(lockLevel, {level})) &*&
            [1/2]node->predSignal |-> _ &*&
            obs(p, obs) &*&
            malloc_block_node(node) &*&
            is_release_ghost_op(rgo, currentThread, inv, p, remove(ob, obs), pre, post) &*&
            pre();
        predicate ghop_post() =
            obs(p, remove(ob, obs)) &*& post(p) &*&
            [frac/2]lock->ghostListId |-> ghostListId &*& [frac/2]lock->level |-> lockLevel;
        lemma void ghop()
            requires lock_inv(lock, inv)() &*& is_atomic_store_int_op(?op, &node->lock, 0, ?P, ?Q) &*& P() &*& ghop_pre() &*& currentThread == releaseThread;
            ensures lock_inv(lock, inv)() &*& is_atomic_store_int_op(op, &node->lock, 0, P, Q) &*& Q() &*& ghop_post();
        {
            open lock_inv(lock, inv)();
            open ghop_pre();
            ghost_list_member_handle_lemma();
            {
                lemma void iter()
                    requires
                        queue(lock, lockLevel, inv, ghostListId, ?nsig, ?nl, ?n, ?ns) &*& mem(node, ns) == true &*&
                        ghost_list_member_handle(ghostListId, node) &*&
                        [1/2]node->lock |-> 1 &*&
                        [1/2]node->pred |-> 0 &*&
                        [1/2]node->frac |-> frac &*&
                        [1/2]node->predSignal |-> _ &*&
                        [1/2]node->signal |-> ?signal &*&
                        [1/2]node->level |-> ?level &*& ob == pair(signal, append(lockLevel, {level})) &*&
                        obs(p, obs) &*&
                        malloc_block_node(node) &*&
                        is_release_ghost_op(rgo, currentThread, inv, p, remove(ob, obs), pre, post) &*& pre() &*&
                        is_atomic_store_int_op(op, &node->lock, 0, P, Q) &*& P();
                    ensures
                        obs(p, remove(ob, obs)) &*& post(p) &*&
                        queue(lock, lockLevel, inv, ghostListId, nsig, nl, n, ns) &*&
                        is_atomic_store_int_op(op, &node->lock, 0, P, Q) &*& Q() &*&
                        [frac/4]lock->ghostListId |-> _;
                {
                    open queue(lock, lockLevel, inv, ghostListId, nsig, nl, n, ns);
                    if (n == node) {
                        merge_fractions node_lock(n, _);
                        merge_fractions node_pred(n, _);
                        merge_fractions node_frac(n, _);
                        merge_fractions node_level(n, _);
                        merge_fractions node_predSignal(n, _);
                        merge_fractions node_signal(n, _);
                        open queue(lock, lockLevel, inv, ghostListId, _, _, 0, _);
                        op();
                        set_signal(node->signal);
                        leak signal(_, _, true);
                        is_ancestor_of_refl(p);
                        rgo();
                        leak is_release_ghost_op(rgo, currentThread, inv, p, remove(ob, obs), pre, post);
                    } else {
                        iter();
                    }
                    close queue(lock, lockLevel, inv, ghostListId, nsig, nl, n, ns);
                }
                iter();
            }
            close lock_inv(lock, inv)();
            close ghop_post();
        }
        @*/
        //@ close ghop_pre();
        //@ produce_lemma_function_pointer_chunk(ghop) : atomic_store_int_ghost_op(lock_inv(lock, inv), &node->lock, 0, ghop_pre, ghop_post, currentThread)() { call(); };
        atomic_store_int(&node->lock, 0);
        //@ leak is_atomic_store_int_ghost_op(ghop, _, _, _, _, _, _);
        //@ open ghop_post();
    }
    thread->node = thread->pred;
    //@ close [frac]lock(lock, lockLevel, inv);
    //@ close lock_thread(thread);
    //@ is_ancestor_of_refl(p);
}

void release(struct lock_thread *thread)
    //@ requires locked(thread, ?lock, ?lockLevel, ?inv, ?frac, ?ob) &*& inv() &*& obs(?p, ?obs);
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
    free(thread->node);
    free(thread);
}

void dispose_lock(struct lock *lock)
    //@ requires lock(lock, ?lockLevel, ?inv);
    //@ ensures inv();
    //@ terminates;
{
    //@ open lock(lock, lockLevel, inv);
    //@ destroy_atomic_space();
    //@ open lock_inv(lock, inv)();
    //@ open queue(lock, _, inv, _, _, _, _, _);
    free(lock->tail);
    free(lock);
    //@ leak ghost_list(_, _) &*& ghost_list_member_handle(_, _);
}
