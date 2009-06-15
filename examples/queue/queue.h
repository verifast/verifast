#ifndef QUEUE_H
#define QUEUE_H

#include "atomics.h"
#include "list.h"

struct queue;

/*@

predicate queue_state(struct queue *queue, list<void *> values);
predicate queue_consumer(struct queue *queue);

@*/

struct queue *create_queue();
    //@ requires emp;
    //@ ensures queue_consumer(result) &*& queue_state(result, nil);

/*@

predicate_family queue_enqueue_operation_pre(void *op)(any info, struct queue *queue, void *value);
predicate_family queue_enqueue_operation_post(void *op)(any info, bool success);

typedef lemma bool queue_enqueue_operation();
    requires queue_enqueue_operation_pre(this)(?info, ?queue, ?value) &*& queue_state(queue, ?values);
    ensures queue_enqueue_operation_post(this)(info, result) &*& queue_state(queue, result ? append(values, cons(value, nil)) : values);

predicate_family queue_enqueue_context_pre(void *ctxt)(any info, predicate() inv, struct queue *queue, void *value);
predicate_family queue_enqueue_context_post(void *ctxt)(any info);

typedef lemma bool queue_enqueue_context(queue_enqueue_operation *op);
    requires
        queue_enqueue_context_pre(this)(?info, ?inv, ?queue, ?value) &*& inv() &*&
        is_queue_enqueue_operation(op) &*&
        queue_enqueue_operation_pre(op)(?opInfo, queue, value);
    ensures
        queue_enqueue_operation_post(op)(opInfo, result) &*& inv() &*&
        is_queue_enqueue_operation(op) &*&
        result ?
            queue_enqueue_context_post(this)(info)
        :
            queue_enqueue_context_pre(this)(info, inv, queue, value);

@*/

void queue_enqueue(struct queue *queue, void *value);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        queue_enqueue_context_pre(?ctxt)(?info, inv, queue, value) &*&
        is_queue_enqueue_context(ctxt);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        queue_enqueue_context_post(ctxt)(info) &*&
        is_queue_enqueue_context(ctxt);
    @*/

/*@

predicate_family queue_try_dequeue_operation_pre(void *op)(any info, struct queue *queue);
predicate_family queue_try_dequeue_operation_post(void *op)(any info, bool success, void *value);

typedef lemma bool queue_try_dequeue_operation();
    requires queue_try_dequeue_operation_pre(this)(?info, ?queue) &*& queue_state(queue, ?values);
    ensures
        switch (values) {
            case nil: return queue_try_dequeue_operation_post(this)(info, false, _) &*& queue_state(queue, nil);
            case cons(h, t): return queue_try_dequeue_operation_post(this)(info, true, h) &*& queue_state(queue, t);
        };

predicate_family queue_try_dequeue_context_pre(void *ctxt)(any info, predicate() inv, struct queue *queue);
predicate_family queue_try_dequeue_context_post(void *ctxt)(any info, bool result, void *value);

typedef lemma bool queue_try_dequeue_context(queue_try_dequeue_operation *op);
    requires
        queue_try_dequeue_context_pre(this)(?info, ?inv, ?queue) &*& inv() &*&
        is_queue_try_dequeue_operation(op) &*&
        queue_try_dequeue_operation_pre(op)(?opInfo, queue);
    ensures
        queue_try_dequeue_operation_post(op)(opInfo, result, ?value) &*& inv() &*&
        is_queue_try_dequeue_operation(op) &*&
        queue_try_dequeue_context_post(this)(info, result, value);

@*/

bool queue_try_dequeue(struct queue *queue, void **pvalue);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        queue_try_dequeue_context_pre(?ctxt)(?info, inv, queue) &*&
        is_queue_try_dequeue_context(ctxt) &*&
        queue_consumer(queue) &*& pointer(pvalue, _);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        queue_try_dequeue_context_post(ctxt)(info, result, ?value0) &*&
        is_queue_try_dequeue_context(ctxt) &*&
        pointer(pvalue, ?value) &*& queue_consumer(queue) &*& result ? value0 == value : true;
    @*/

void queue_dispose(struct queue *queue);
    //@ requires queue_consumer(queue) &*& queue_state(queue, _);
    //@ ensures emp;

#endif
