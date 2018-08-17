#ifndef CHANNELS_H
#define CHANNELS_H

//@ #include "abstract_io.gh"
//@ #include "sequences.gh"

/*@

// The development is generic in the type of elements; however, due to limitations of the current VeriFast implementation,
// for now we need to instantiate the element type.

#define T list<char>

@*/

struct channel;
typedef struct channel *channel;

/*@

predicate send_(predicate() P, channel c, predicate(void *; T) msgPred, fixpoint(nat, T) msgs);

predicate receive_(predicate() P, channel c, predicate(void *; T) msgPred, fixpoint(nat, T) msgs);

@*/

void channel_send(channel c, void *msgPtr);
    //@ requires send_(?P, c, ?msgPred, ?msgs) &*& msgPred(msgPtr, ?msg) &*& token(P) &*& msgs(zero) == msg;
    //@ ensures token(?Q) &*& send_(Q, c, msgPred, (tail_)(msgs));

void *channel_receive(channel c);
    //@ requires receive_(?P, c, ?msgPred, ?msgs) &*& token(P);
    //@ ensures receive_(?Q, c, msgPred, (tail_)(msgs)) &*& token(Q) &*& msgPred(result, msgs(zero));

#endif
