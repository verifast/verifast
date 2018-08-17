#ifndef QUEUES_H
#define QUEUES_H

struct queue;
typedef struct queue *queue;

//@ predicate queue<t>(queue queue, predicate(void *; t) pred; list<t> elems);

//@ predicate create_queue_ghost_args<t>(predicate(void *; t) pred) = true;

queue create_queue/*@ <t> @*/();
    //@ requires create_queue_ghost_args<t>(?pred);
    //@ ensures queue(result, pred, nil);

void queue_enqueue/*@ <t> @*/(queue queue, void *elem);
    //@ requires queue<t>(queue, ?pred, ?elems) &*& pred(elem, ?v);
    //@ ensures queue<t>(queue, pred, append(elems, {v}));

bool queue_is_empty/*@ <t> @*/(queue queue);
    //@ requires [?f]queue<t>(queue, ?pred, ?elems);
    //@ ensures [f]queue<t>(queue, pred, elems) &*& result == (elems == nil);

void *queue_dequeue/*@ <t> @*/(queue queue);
    //@ requires queue<t>(queue, ?pred, cons(?v, ?elems));
    //@ ensures queue<t>(queue, pred, elems) &*& pred(result, v);

#endif
