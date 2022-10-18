#include <stdlib.h>
#include <threading.h>
//@ #include "ghost_cells.gh"
#include "queues.h"
#include "prophecies.h"
#include "channels_local.h"

// Some auxiliary theory on interleavings

/*@

lemma void contains_interleavings_apply<t>(fixpoint(nat, t) seq1, fixpoint(nat, t) seq2, fixpoint(nat, t) seq3)
    requires contains_interleavings<t>(?p, ?p1, ?p2) &*& p1(seq1) && p2(seq2) && is_interleaving(seq1, seq2, seq3) || p1(seq1) && seq3 == seq1 || p2(seq2) && seq3 == seq2;
    ensures contains_interleavings<t>(p, p1, p2) &*& p(seq3) == true;
{
    open contains_interleavings(_, _, _);
    assert [_]is_forall_t(?forall_triples);
    forall_t_elim(forall_triples, (contains_interleavings_)(p, p1, p2), triple(seq1, seq2, seq3));
    close contains_interleavings(p, p1, p2);
}

lemma void contains_interleavings_left_lemma<t>(fixpoint(fixpoint(nat, t), bool) p, fixpoint(fixpoint(nat, t), bool) p1, fixpoint(fixpoint(nat, t), bool) p2, t value, fixpoint(nat, t) witness)
    requires contains_interleavings<t>(p, p1, p2) &*& p1((cons_)(value, witness)) == true;
    ensures contains_interleavings((contains_cons_)(p, value), (contains_cons_)(p1, value), p2);
{
    open contains_interleavings<t>(p, p1, p2);
    assert [_]is_forall_t<triple<fixpoint(nat, t)> >(?forall_triples);
    if (!forall_triples((contains_interleavings_)((contains_cons_)(p, value), (contains_cons_)(p1, value), p2))) {
        triple<fixpoint(nat, t)> seqs = not_forall_t(forall_triples, (contains_interleavings_)((contains_cons_)(p, value), (contains_cons_)(p1, value), p2));
        assert seqs == triple(?seq1, ?seq2, ?seq3);
        if (contains_cons_(p1, value, seq1) && seq3 == seq1) {
            forall_t_elim(forall_triples, (contains_interleavings_)(p, p1, p2), triple((cons_)(value, seq1), seq2, (cons_)(value, seq3)));
        } else if (p2(seq2) && seq3 == seq2) {
            is_interleaving_def((cons_)(value, witness), seq2, (cons_)(value, seq3));
            is_interleaving_trivial2(witness, seq2);
            tail_cons_eq(value, seq3);
            tail_cons_eq(value, seq1);
            tail_cons_eq(value, seq2);
            tail_cons_eq(value, witness);
            forall_t_elim(forall_triples, (contains_interleavings_)(p, p1, p2), triple((cons_)(value, witness), seq2, (cons_)(value, seq3)));
        } else {
            is_interleaving_def((cons_)(value, seq1), seq2, (cons_)(value, seq3));
            tail_cons_eq(value, seq1);
            tail_cons_eq(value, seq3);
            assert is_interleaving((cons_)(value, seq1), seq2, (cons_)(value, seq3)) == true;
            forall_t_elim(forall_triples, (contains_interleavings_)(p, p1, p2), triple((cons_)(value, seq1), seq2, (cons_)(value, seq3)));
        }
    }
    close contains_interleavings((contains_cons_)(p, value), (contains_cons_)(p1, value), p2);
}

lemma void contains_interleavings_right_lemma<t>(fixpoint(fixpoint(nat, t), bool) p, fixpoint(fixpoint(nat, t), bool) p1, fixpoint(fixpoint(nat, t), bool) p2, t value, fixpoint(nat, t) witness)
    requires contains_interleavings<t>(p, p1, p2) &*& p2((cons_)(value, witness)) == true;
    ensures contains_interleavings((contains_cons_)(p, value), p1, (contains_cons_)(p2, value));
{
    open contains_interleavings<t>(p, p1, p2);
    assert [_]is_forall_t<triple<fixpoint(nat, t)> >(?forall_triples);
    if (!forall_triples((contains_interleavings_)((contains_cons_)(p, value), p1, (contains_cons_)(p2, value)))) {
        triple<fixpoint(nat, t)> seqs = not_forall_t(forall_triples, (contains_interleavings_)((contains_cons_)(p, value), p1, (contains_cons_)(p2, value)));
        assert seqs == triple(?seq1, ?seq2, ?seq3);
        if (contains_cons_(p2, value, seq2) && seq3 == seq2) {
            forall_t_elim(forall_triples, (contains_interleavings_)(p, p1, p2), triple(seq1, (cons_)(value, seq2), (cons_)(value, seq3)));
        } else if (p1(seq1) && seq3 == seq1) {
            is_interleaving_def(seq1, (cons_)(value, witness), (cons_)(value, seq3));
            is_interleaving_trivial1(seq1, witness);
            tail_cons_eq(value, seq3);
            tail_cons_eq(value, seq1);
            tail_cons_eq(value, seq2);
            tail_cons_eq(value, witness);
            forall_t_elim(forall_triples, (contains_interleavings_)(p, p1, p2), triple(seq1, (cons_)(value, witness), (cons_)(value, seq3)));
        } else {
            is_interleaving_def(seq1, (cons_)(value, seq2), (cons_)(value, seq3));
            tail_cons_eq(value, seq2);
            tail_cons_eq(value, seq3);
            assert is_interleaving(seq1, (cons_)(value, seq2), (cons_)(value, seq3)) == true;
            forall_t_elim(forall_triples, (contains_interleavings_)(p, p1, p2), triple(seq1, (cons_)(value, seq2), (cons_)(value, seq3)));
        }
    }
    close contains_interleavings((contains_cons_)(p, value), p1, (contains_cons_)(p2, value));
}

@*/

// Channels

struct channel {
    mutex mutex;
    mutex_cond cond;
    queue queue;
    //@ predicate(void *; T) pred;
    //@ int senderTree;
    prophecy_var_t prophecyVar;
};

/*@

inductive senderNode = leaf(fixpoint(fixpoint(nat, T), bool) p) | split(int pCell, int left, int right);

predicate split_node(int senderTree, fixpoint(fixpoint(nat, T), bool) p) =
    [_]ghost_cell<senderNode>(senderTree, split(?pCell, ?left, ?right)) &*&
    exists<bool>(?isLeft) &*&
    isLeft ?
        sender_node(left, p)
    :
        sender_node(right, p);

predicate sender_node(int senderTree, fixpoint(fixpoint(nat, T), bool) p) =
    exists<bool>(?isLeaf) &*&
    isLeaf ?
        [1/2]ghost_cell<senderNode>(senderTree, leaf(p))
    :
        split_node(senderTree, p);

predicate valid_elems(fixpoint(fixpoint(nat, T), bool) rp, list<T> elems, fixpoint(fixpoint(nat, T), bool) sp) =
    switch (elems) {
        case nil: return sp == rp;
        case cons(elem, elems0): return
            exists<fixpoint(nat, T)>(?witness) &*& rp((cons_)(elem, witness)) == true &*&
            valid_elems((contains_cons_)(rp, elem), elems0, sp);
    };

lemma void valid_elems_send_lemma(T value, fixpoint(nat, T) witness)
    requires valid_elems(?rp, ?elems, ?sp) &*& sp((cons_)(value, witness)) == true;
    ensures valid_elems(rp, append(elems, {value}), (contains_cons_)(sp, value));
{
    open valid_elems(rp, elems, sp);
    switch (elems) {
        case nil:
            close valid_elems((contains_cons_)(sp, value), nil, (contains_cons_)(sp, value));
            close exists(witness);
        case cons(elem, elems0):
            valid_elems_send_lemma(value, witness);
    }
    close valid_elems(rp, append(elems, {value}), (contains_cons_)(sp, value));
}

predicate sender_tree(int senderTree, fixpoint(fixpoint(nat, T), bool) sender_p) =
    exists<bool>(?isLeaf) &*&
    isLeaf ?
        [1/2]ghost_cell(senderTree, leaf(sender_p))
    :
        [_]ghost_cell(senderTree, split(?pcell, ?left, ?right)) &*& ghost_cell(pcell, sender_p) &*&
        sender_tree(left, ?pleft) &*& sender_tree(right, ?pright) &*&
        contains_interleavings(sender_p, pleft, pright);

predicate_ctor channel_inv(channel c)() =
    [_]c->pred |-> ?pred &*&
    [_]c->queue |-> ?q &*& queue<T>(q, pred, ?elems) &*&
    [_]c->senderTree |-> ?senderTree &*& sender_tree(senderTree, ?sender_p) &*&
    [_]c->prophecyVar |-> ?pvar &*& [1/2]prophecy_var<T>(pvar, ?rp, pred, _) &*&
    valid_elems(rp, elems, sender_p);

predicate channel_sender(channel c, predicate(void *; T) pred, fixpoint(fixpoint(nat, T), bool) p) =
    [_]c->mutex |-> ?mutex &*& [_]mutex(mutex, channel_inv(c)) &*& [_]c->pred |-> pred &*& [_]c->senderTree |-> ?senderTree &*&
    sender_node(senderTree, p) &*&
    [_]c->cond |-> ?cond &*& [_]mutex_cond(cond, mutex);

predicate channel_receiver(channel c, predicate(void *; T) pred, fixpoint(nat, T) msgs) =
    [_]c->mutex |-> ?mutex &*& [_]mutex(mutex, channel_inv(c)) &*& [_]c->pred |-> pred &*&
    [_]c->prophecyVar |-> ?pvar &*& [1/2]prophecy_var<T>(pvar, _, pred, msgs) &*&
    [_]c->cond |-> ?cond &*& [_]mutex_cond(cond, mutex) &*& malloc_block_channel(c);

lemma void split_lemma()
    requires sender_node(?senderTree, ?pLeaf) &*& sender_tree(senderTree, ?pRoot) &*& contains_interleavings(pLeaf, ?pLeft, ?pRight);
    ensures sender_node(senderTree, pLeft) &*& sender_node(senderTree, pRight) &*& sender_tree(senderTree, pRoot);
{
    open sender_node(senderTree, pLeaf);
    open exists<bool>(?isLeaf);
    open sender_tree(senderTree, pRoot);
    open exists<bool>(_);
    if (isLeaf) {
        int pcell = create_ghost_cell<fixpoint(fixpoint(nat, T), bool)>(pRoot);
        int left = create_ghost_cell<senderNode>(leaf(pLeft));
        close exists<bool>(true);
        close sender_node(left, pLeft);
        close exists<bool>(true);
        close sender_tree(left, pLeft);
        int right = create_ghost_cell<senderNode>(leaf(pRight));
        close exists<bool>(true);
        close sender_node(right, pRight);
        close exists<bool>(true);
        close sender_tree(right, pRight);
        ghost_cell_mutate(senderTree, split(pcell, left, right));
        ghost_cell_leak(senderTree);
        close exists<bool>(true);
        close split_node(senderTree, pLeft);
        close exists<bool>(false);
        close split_node(senderTree, pRight);
    } else {
        open split_node(senderTree, pLeaf);
        open exists<bool>(?isLeft);
        split_lemma();
        close exists<bool>(isLeft);
        close split_node(senderTree, pLeft);
        close exists<bool>(isLeft);
        close split_node(senderTree, pRight);
    }
    close exists<bool>(false);
    close sender_tree(senderTree, pRoot);
    close exists<bool>(false);
    close sender_node(senderTree, pLeft);
    close exists<bool>(false);
    close sender_node(senderTree, pRight);
}

lemma void channel_sender_split(fixpoint(fixpoint(nat, T), bool) p1, fixpoint(fixpoint(nat, T), bool) p2) nonghost_callers_only
    requires channel_sender(?c, ?pred, ?p) &*& contains_interleavings(p, p1, p2);
    ensures channel_sender(c, pred, p1) &*& channel_sender(c, pred, p2);
{
    open channel_sender(c, pred, p);
    int senderTree = c->senderTree;
    {
        predicate pre() = [_]c->senderTree |-> senderTree &*& sender_node(senderTree, p) &*& contains_interleavings(p, p1, p2);
        predicate post() = sender_node(senderTree, p1) &*& sender_node(senderTree, p2);
        produce_lemma_function_pointer_chunk mutex_ghost_critical_section_t(channel_inv(c), pre, post)() {
            open pre();
            open channel_inv(c)();
            split_lemma();
            close channel_inv(c)();
            close post();
        } {
            close pre();
            mutex_ghost_use(c->mutex, pre, post);
            open post();
        }
    }
    close channel_sender(c, pred, p1);
    close channel_sender(c, pred, p2);
}

lemma void channel_sender_to_send_(fixpoint(fixpoint(nat, T), bool) p, fixpoint(nat, T) msgs)
    requires channel_sender(?c, ?pred, p) &*& p(msgs) == true;
    ensures token(?P) &*& send_(P, c, pred, msgs);
{
    close True();
    close token(True);
    close send_(True, c, pred, msgs);
}

lemma void channel_receiver_to_receive_()
    requires channel_receiver(?c, ?pred, ?msgs);
    ensures token(?P) &*& receive_(P, c, pred, msgs);
{
    close True();
    close token(True);
    close receive_(True, c, pred, msgs);
}

@*/

channel create_channel()
    //@ requires create_channel_ghost_args(?p, ?witness, ?pred) &*& (p)(witness) == true;
    //@ ensures channel_sender(result, pred, p) &*& channel_receiver(result, pred, ?msgs) &*& (p)(msgs) == true;
{
    //@ open create_channel_ghost_args(p, witness, pred);
    channel c = malloc(sizeof(struct channel));
    if (c == 0) abort();
    //@ c->pred = pred;
    //@ close create_queue_ghost_args(pred);
    queue queue = create_queue();
    c->queue = queue;
    //@ int senderTree = create_ghost_cell<senderNode>(leaf(p));
    //@ c->senderTree = senderTree;
    //@ close exists<bool>(true);
    //@ close sender_tree(senderTree, p);
    //@ close create_prophecy_var_ghost_args(p, witness, pred);
    prophecy_var_t prophecyVar = create_prophecy_var();
    //@ assert prophecy_var(prophecyVar, p, pred, ?msgs);
    c->prophecyVar = prophecyVar;
    //@ close valid_elems(p, nil, p);
    //@ leak c->pred |-> ?_ &*& c->queue |-> ?_ &*& c->senderTree |-> ?_ &*& c->prophecyVar |-> ?_;
    //@ close channel_inv(c)();
    //@ close create_mutex_ghost_arg(channel_inv(c));
    mutex mutex = create_mutex();
    c->mutex = mutex;
    //@ close create_mutex_cond_ghost_args(mutex);
    mutex_cond cond = create_mutex_cond();
    c->cond = cond;
    //@ leak c->mutex |-> ?_ &*& mutex(mutex, _) &*& c->cond |-> ?_ &*& mutex_cond(cond, mutex);
    return c;
    //@ close exists(true);
    //@ close sender_node(senderTree, p);
    //@ close channel_sender(c, pred, p);
    //@ close channel_receiver(c, pred, msgs);
}

/*@

lemma void send_lemma(T value, fixpoint(nat, T) witness)
    requires sender_node(?senderTree, ?pLeaf) &*& sender_tree(senderTree, ?pRoot) &*& pLeaf((cons_)(value, witness)) == true;
    ensures sender_node(senderTree, (contains_cons_)(pLeaf, value)) &*& sender_tree(senderTree, (contains_cons_)(pRoot, value)) &*& pRoot((cons_)(value, witness)) == true;
{
    open sender_node(senderTree, pLeaf);
    open exists<bool>(?isLeaf);
    open sender_tree(senderTree, pRoot);  
    open exists<bool>(_);  
    if (isLeaf) {
        ghost_cell_mutate(senderTree, leaf((contains_cons_)(pLeaf, value)));
    } else {
        open split_node(senderTree, pLeaf);
        assert exists<bool>(?isLeft);
        assert [_]ghost_cell(senderTree, split(?pcell, ?left, ?right));
        assert sender_tree(left, ?pLeft) &*& sender_tree(right, ?pRight);
        send_lemma(value, witness);
        ghost_cell_mutate<fixpoint(fixpoint(nat, T), bool)>(pcell, (contains_cons_)(pRoot, value));
        if (isLeft) {
            contains_interleavings_left_lemma(pRoot, pLeft, pRight, value, witness);
            assert contains_interleavings((contains_cons_)(pRoot, value), (contains_cons_)(pLeft, value), pRight);
            contains_interleavings_apply(witness, witness, witness);
        } else {
            contains_interleavings_right_lemma(pRoot, pLeft, pRight, value, witness);
            assert contains_interleavings((contains_cons_)(pRoot, value), pLeft, (contains_cons_)(pRight, value));
            contains_interleavings_apply(witness, witness, witness);
        }
        close split_node(senderTree, (contains_cons_)(pLeaf, value));
    }
    close exists(isLeaf);
    close exists(isLeaf);
    close sender_node(senderTree, (contains_cons_)(pLeaf, value));
    close sender_tree(senderTree, (contains_cons_)(pRoot, value));
}

@*/

void channel_send(channel c, void *msgPtr)
    // requires channel_sender<t>(c, ?pred, ?p) &*& pred(msg, ?v) &*& exists<fixpoint(nat, t)>(?seq) &*& p(cons_(v, seq)) == true;
    // ensures channel_sender<t>(c, pred, (contains_cons_)(p, v));
    //@ requires send_(?P, c, ?msgPred, ?msgs) &*& msgPred(msgPtr, ?msg) &*& token(P) &*& msgs(zero) == msg;
    //@ ensures token(?Q) &*& send_(Q, c, msgPred, (tail_)(msgs));
{
    //@ open send_(P, c, msgPred, msgs);
    //@ open channel_sender(c, msgPred, ?p);
    mutex_acquire(c->mutex);
    //@ open channel_inv(c)();
    queue_enqueue(c->queue, msgPtr);
    mutex_cond_signal(c->cond);
    //@ eq_cons_tail(msgs);
    //@ send_lemma(msg, (tail_)(msgs));
    //@ valid_elems_send_lemma(msg, (tail_)(msgs));
    //@ close channel_inv(c)();
    mutex_release(c->mutex);
    //@ close channel_sender(c, msgPred, (contains_cons_)(p, msg));
    //@ close send_(P, c, msgPred, (tail_)(msgs));
}

void *channel_receive(channel c)
    // requires channel_receiver<t>(c, ?pred, ?seq);
    // ensures channel_receiver<t>(c, pred, tail_(seq)) &*& pred(result, seq(zero));
    //@ requires receive_(?P, c, ?msgPred, ?msgs) &*& token(P);
    //@ ensures receive_(?Q, c, msgPred, (tail_)(msgs)) &*& token(Q) &*& msgPred(result, msgs(zero));
{
    //@ open receive_(P, c, msgPred, msgs);
    //@ open channel_receiver(c, msgPred, msgs);
    //@ assert [_]c->mutex |-> ?mutex &*& [?f]mutex(mutex, channel_inv(c));
    mutex_acquire(c->mutex);
    for (;;)
        /*@
        invariant
            [_]c->mutex |-> mutex &*& mutex_held(mutex, channel_inv(c), currentThread, f) &*& [_]c->pred |-> msgPred &*&
            [_]c->prophecyVar |-> ?pvar &*& [1/2]prophecy_var<T>(pvar, _, msgPred, msgs) &*&
            [_]c->cond |-> ?cond &*& [_]mutex_cond(cond, mutex) &*& malloc_block_channel(c) &*&
            channel_inv(c)();
        @*/
    {
        //@ open channel_inv(c)();
        if (!queue_is_empty(c->queue))
            break;
        //@ close channel_inv(c)();
        mutex_cond_wait(c->cond, c->mutex);
    }
    void *elem = queue_dequeue(c->queue);
    //@ open valid_elems(?rp, ?elems, ?sp);
    //@ open exists(?witness);
    //@ close prophecy_var_assign_ghost_args(witness);
    prophecy_var_assign(c->prophecyVar, elem);
    //@ close channel_inv(c)();
    mutex_release(c->mutex);
    return elem;
    //@ close channel_receiver(c, msgPred, (tail_)(msgs));
    //@ close receive_(P, c, msgPred, (tail_)(msgs));
}

