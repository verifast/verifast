#ifndef CHANNELS_LOCAL_H
#define CHANNELS_LOCAL_H

//@ #include "quantifiers.gh"
#include "channels.h"

/*@

predicate channel_sender(channel c, predicate(void *; T) pred, fixpoint(fixpoint(nat, T), bool) p);

predicate channel_receiver(channel c, predicate(void *; T) pred, fixpoint(nat, T) msgs);

inductive triple<t> = triple(t, t, t);

fixpoint bool contains_interleavings_<t>(fixpoint(fixpoint(nat, t), bool) p, fixpoint(fixpoint(nat, t), bool) p1, fixpoint(fixpoint(nat, t), bool) p2, triple<fixpoint(nat, t)> seqs) {
    switch (seqs) {
        case triple(seq1, seq2, seq3): return
            !(p1(seq1) && p2(seq2) && is_interleaving(seq1, seq2, seq3) || p1(seq1) && seq3 == seq1 || p2(seq2) && seq3 == seq2) ||
            p(seq3) == true;
    }
}

predicate contains_interleavings<t>(fixpoint(fixpoint(nat, t), bool) p, fixpoint(fixpoint(nat, t), bool) p1, fixpoint(fixpoint(nat, t), bool) p2) =
    [_]is_forall_t<triple<fixpoint(nat, t)> >(?forall_triples) &*& forall_triples((contains_interleavings_)(p, p1, p2)) == true;

lemma void channel_sender_split(fixpoint(fixpoint(nat, T), bool) p1, fixpoint(fixpoint(nat, T), bool) p2);
    nonghost_callers_only
    requires channel_sender(?c, ?pred, ?p) &*& contains_interleavings(p, p1, p2);
    ensures channel_sender(c, pred, p1) &*& channel_sender(c, pred, p2);

predicate send_(predicate() P, channel c, predicate(void *; T) msgPred, fixpoint(nat, T) msgs) =
    channel_sender(c, msgPred, ?p) &*& p(msgs) == true;

lemma void channel_sender_to_send_(fixpoint(fixpoint(nat, T), bool) p, fixpoint(nat, T) msgs);
    requires channel_sender(?c, ?pred, p) &*& p(msgs) == true;
    ensures token(?P) &*& send_(P, c, pred, msgs);

predicate receive_(predicate() P, channel c, predicate(void *; T) msgPred, fixpoint(nat, T) msgs) =
    channel_receiver(c, msgPred, msgs);

lemma void channel_receiver_to_receive_();
    requires channel_receiver(?c, ?pred, ?msgs);
    ensures token(?P) &*& receive_(P, c, pred, msgs);

@*/

//@ predicate create_channel_ghost_args(fixpoint(fixpoint(nat, T), bool) p, fixpoint(nat, T) witness, predicate(void *; T) pred) = true;

channel create_channel();
    //@ requires create_channel_ghost_args(?p, ?witness, ?pred) &*& (p)(witness) == true;
    //@ ensures channel_sender(result, pred, p) &*& channel_receiver(result, pred, ?msgs) &*& (p)(msgs) == true;

#endif
