#ifndef QUEUE_H
#define QUEUE_H

#include "atomics.h"

struct queue;

/*@

predicate queue_state(struct queue *queue, list<void *> values);
predicate queue_consumer(struct queue *queue);

@*/

struct queue *create_queue();
    //@ requires emp;
    //@ ensures queue_consumer(result) &*& queue_state(result, nil);

/*@

typedef lemma void queue_enqueue_operation(struct queue *queue, void *value, predicate() pre, predicate(bool) post)();
    requires queue_state(queue, ?values) &*& pre();
    ensures post(?result) &*& queue_state(queue, result ? append(values, cons(value, nil)) : values);

typedef lemma void queue_enqueue_context(predicate() inv, struct queue *queue, void *value, predicate() pre, predicate() post)();
    requires inv() &*& is_queue_enqueue_operation(?op, queue, value, ?P, ?Q) &*& P() &*& pre();
    ensures inv() &*& is_queue_enqueue_operation(op, queue, value, P, Q) &*& Q(?result) &*&
        result ? post() : pre();

@*/

void queue_enqueue(struct queue *queue, void *value);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_queue_enqueue_context(?ctxt, inv, queue, value, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_queue_enqueue_context(ctxt, inv, queue, value, pre, post) &*& post();
    @*/

/*@

typedef lemma void queue_try_dequeue_operation(struct queue *queue, predicate() pre, predicate(bool, void *) post)();
    requires queue_state(queue, ?values) &*& pre();
    ensures
        switch (values) {
            case nil: return queue_state(queue, nil) &*& post(false, _);
            case cons(h, t): return queue_state(queue, t) &*& post(true, h);
        };

typedef lemma void queue_try_dequeue_context(predicate() inv, struct queue *queue, predicate() pre, predicate(bool, void *) post)();
    requires inv() &*& is_queue_try_dequeue_operation(?op, queue, ?P, ?Q) &*& P() &*& pre();
    ensures inv() &*& is_queue_try_dequeue_operation(op, queue, P, Q) &*& Q(?result, ?value) &*& post(result, value);

@*/

bool queue_try_dequeue(struct queue *queue, void **pvalue);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_queue_try_dequeue_context(?ctxt, inv, queue, ?pre, ?post) &*& pre() &*&
        queue_consumer(queue) &*& pointer(pvalue, _);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_queue_try_dequeue_context(ctxt, inv, queue, pre, post) &*& post(result, ?value0) &*&
        pointer(pvalue, ?value) &*& queue_consumer(queue) &*& result ? value0 == value : true;
    @*/

void queue_dispose(struct queue *queue);
    //@ requires queue_consumer(queue) &*& queue_state(queue, _);
    //@ ensures emp;

#endif
