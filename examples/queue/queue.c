#include "stdlib.h"
#include "atomics.h"
#include "list.h"
#include "listex.h"
#include "queue.h"

/* A lock-free queue. Multiple enqueueers, single dequeueer.
 * Should be memory-safe, data-race-free, functionally correct, and not leak memory.
 * Time complexity: enqueue: O(1) (assuming no contention). Dequeue: amortized O(1)
 * Progress:
 * - enqueue: obstruction-free (one thread always makes progress) but not wait-free (starvation is possible if there are multiple enqueueers)
 * - dequeue: wait-free (assuming there is an element available, of course)
 */

struct node {
    struct node *next;
    void *value;
};

struct queue {
    struct node *first;
    struct node *middle;
    struct node *last;
    //@ struct node *ghost_middle;
    //@ list<void *> front_values;
};

/*@

predicate lseg(struct node *first, struct node *last, list<void *> values) =
    first == last ?
        values == nil
    :
        first->next |-> ?next &*& first->value |-> ?head &*& malloc_block_node(first) &*& first != 0 &*& lseg(next, last, ?tail) &*& values == cons(head, tail);

predicate lseg2(struct node *first, struct node *middle, void *value0, list<void *> values) =
    first->value |-> value0 &*& malloc_block_node(first) &*& [1/2]first->next |-> ?next &*&
    (first == middle ? values == nil : [1/2]first->next |-> next &*& lseg2(next, middle, ?head, ?tail) &*& values == cons(head, tail));

lemma void lseg2_distinct(struct node *first, struct node *middle, struct node *n)
    requires lseg2(first, middle, ?value0, ?values) &*& n->next |-> ?nNext;
    ensures lseg2(first, middle, value0, values) &*& n->next |-> nNext &*& n != middle;
{
    open lseg2(first, middle, value0, values);
    if (first != middle) {
        assert [_]first->next |-> ?next;
        lseg2_distinct(next, middle, n);
    }
    close lseg2(first, middle, value0, values);
}

predicate queue_consumer(struct queue *queue) =
    queue->first |-> ?first &*& queue->middle |-> ?middle &*& [1/2]queue->ghost_middle |-> middle &*& malloc_block_queue(queue)
    &*& lseg2(first, middle, _, ?frontValues) &*& [1/2]queue->front_values |-> frontValues;

predicate queue_state(struct queue *queue, list<void *> values) =
    [1/2]queue->ghost_middle |-> ?middle &*& queue->last |-> ?last &*& lseg(last, middle, ?backValues) &*&
    [1/2]middle->next |-> _ &*& [1/2]queue->front_values |-> ?frontValues &*& values == append(frontValues, reverse(backValues));

@*/

struct queue *create_queue()
    //@ requires emp;
    //@ ensures queue_consumer(result) &*& queue_state(result, nil);
{
    struct node *middle = malloc(sizeof(struct node));
    if (middle == 0) { abort(); }
    struct queue *queue = malloc(sizeof(struct queue));
    if (queue == 0) { abort(); }
    queue->first = middle;
    queue->middle = middle;
    queue->last = middle;
    //@ queue->ghost_middle = middle;
    //@ split_fraction queue_ghost_middle(queue, _);
    //@ close lseg(middle, middle, nil);
    //@ split_fraction node_next(middle, _);
    //@ void *middleValue = middle->value;
    //@ close lseg2(middle, middle, middleValue, nil);
    //@ queue->front_values = nil;
    //@ split_fraction queue_front_values(queue, _);
    //@ close queue_consumer(queue);
    //@ close queue_state(queue, nil);
    return queue;
}

/*@

// ***************** begin atomic_compare_and_store_pointer *******************

inductive queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation_info =
    queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation_info(
        atomic_compare_and_store_pointer_operation *op,
        struct node *last,
        struct node *n,
        void *value);

predicate_family_instance queue_enqueue_operation_pre
    (queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation)
    (queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation_info info, struct queue *queue, void *value)
    =
    switch (info) {
        case queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation_info(op, last, n, value_):
            return
                is_atomic_compare_and_store_pointer_operation(op) &*&
                atomic_compare_and_store_pointer_operation_pre(&queue->last, last, n) &*& value_ == value &*&
                n->next |-> last &*& n->value |-> value &*& malloc_block_node(n) &*& n != 0;
    };

predicate_family_instance queue_enqueue_operation_post
    (queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation)
    (queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation_info info, bool result)
    =
    atomic_compare_and_store_pointer_operation_post(result) &*&
    switch (info) {
        case queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation_info(op, last, n, value):
            return
                is_atomic_compare_and_store_pointer_operation(op) &*&
                result ? emp : n->next |-> last &*& n->value |-> value &*& malloc_block_node(n);
    };

lemma bool queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation() : queue_enqueue_operation
    requires queue_enqueue_operation_pre(queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation)(?info, ?queue, ?value) &*& queue_state(queue, ?values);
    ensures queue_enqueue_operation_post(queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation)(info, result) &*& queue_state(queue, result ? append(values, cons(value, nil)) : values);
{
    open queue_enqueue_operation_pre(queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation)(?info_, queue, value);
    open queue_state(queue, values);
    switch (info_) {
        case queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation_info(op, last, n, value_):
            open queue_last(queue, _);
            bool result = op();
            assert pointer(&queue->last, ?last2);
            close queue_last(queue, last2);
            if (result) {
                assert lseg(last, ?middle, ?backValues);
                close lseg(n, middle, cons(value, backValues));
                assert [_]queue_front_values(queue, ?frontValues);
                append_assoc(frontValues, reverse(backValues), cons(value, nil));
            }
            close queue_state(queue, result ? append(values, cons(value, nil)) : values);
            close queue_enqueue_operation_post(queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation)(info_, result);
            return result;
    }
}

inductive queue_enqueue_atomic_compare_and_store_pointer_context_info =
  queue_enqueue_atomic_compare_and_store_pointer_context_info(
      queue_enqueue_context *ctxt, any ctxtInfo, predicate() inv, struct queue *queue, void *value, struct node *last, struct node *n
  );

predicate_family_instance atomic_compare_and_store_pointer_context_pre
    (queue_enqueue_atomic_compare_and_store_pointer_context)
    (queue_enqueue_atomic_compare_and_store_pointer_context_info info, predicate() inv, void **pp, void *old, void *new) =
    switch (info) {
        case queue_enqueue_atomic_compare_and_store_pointer_context_info(ctxt, ctxtInfo, inv_, queue, value, last, n):
            return
                is_queue_enqueue_context(ctxt) &*& queue_enqueue_context_pre(ctxt)(ctxtInfo, inv, queue, value) &*&
                pp == &queue->last &*& old == last &*& new == n &*& inv_ == inv &*& n != 0 &*&
                n->next |-> last &*& n->value |-> value &*& malloc_block_node(n);
    };

predicate_family_instance atomic_compare_and_store_pointer_context_post
    (queue_enqueue_atomic_compare_and_store_pointer_context)
    (queue_enqueue_atomic_compare_and_store_pointer_context_info info, bool success) =
    switch (info) {
        case queue_enqueue_atomic_compare_and_store_pointer_context_info(ctxt, ctxtInfo, inv, queue, value, last, n):
            return
                is_queue_enqueue_context(ctxt) &*&
                success ?
                    queue_enqueue_context_post(ctxt)(ctxtInfo)
                :
                    queue_enqueue_context_pre(ctxt)(ctxtInfo, inv, queue, value) &*&
                    n->next |-> last &*& n->value |-> value &*& malloc_block_node(n);
    };

lemma void queue_enqueue_atomic_compare_and_store_pointer_context(atomic_compare_and_store_pointer_operation *op) : atomic_compare_and_store_pointer_context
    requires
        atomic_compare_and_store_pointer_context_pre(queue_enqueue_atomic_compare_and_store_pointer_context)(?info, ?inv, ?pp, ?old, ?new) &*&
        inv() &*&
        is_atomic_compare_and_store_pointer_operation(op) &*&
        atomic_compare_and_store_pointer_operation_pre(pp, old, new);
    ensures
        atomic_compare_and_store_pointer_context_post(queue_enqueue_atomic_compare_and_store_pointer_context)(info, ?success) &*&
        inv() &*&
        is_atomic_compare_and_store_pointer_operation(op) &*&
        atomic_compare_and_store_pointer_operation_post(success);
{
    open atomic_compare_and_store_pointer_context_pre(queue_enqueue_atomic_compare_and_store_pointer_context)(?info_, inv, pp, old, new);
    switch (info_) {
        case queue_enqueue_atomic_compare_and_store_pointer_context_info(ctxt, ctxtInfo, inv_, queue, value, last, n):
            close
                queue_enqueue_operation_pre
                (queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation)
                (queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation_info(op, last, n, value), queue, value);
            bool success = false;
            produce_lemma_function_pointer_chunk(queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation) {
              success = ctxt(queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation);
            }
            open
                queue_enqueue_operation_post
                (queue_enqueue_atomic_compare_and_store_pointer_queue_enqueue_operation)
                (_, _);
            close atomic_compare_and_store_pointer_context_post(queue_enqueue_atomic_compare_and_store_pointer_context)(info_, success);
    }
}

// ***************** end atomic_compare_and_store_pointer *******************

@*/

void queue_enqueue(struct queue *queue, void *value)
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_queue_enqueue_context(?ctxt) &*&
        queue_enqueue_context_pre(ctxt)(?info, inv, queue, value);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        queue_enqueue_context_post(ctxt)(info) &*&
        is_queue_enqueue_context(ctxt);
    @*/
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->value = value;
    bool done = false;
    while (!done)
        //@ invariant is_queue_enqueue_context(ctxt) &*& [f]atomic_space(inv) &*& (done ? queue_enqueue_context_post(ctxt)(info) : n->next |-> _ &*& n->value |-> value &*& malloc_block_node(n) &*& queue_enqueue_context_pre(ctxt)(info, inv, queue, value));
    {
        struct node *last = 0;
        {
            /*@
            predicate_family_instance atomic_load_pointer_context_pre(context)(unit info_, predicate() inv_, void **pp) =
                is_queue_enqueue_context(ctxt) &*& queue_enqueue_context_pre(ctxt)(info, inv_, queue, value) &*& inv_ == inv &*& pp == &queue->last;

            predicate_family_instance atomic_load_pointer_context_post(context)(unit info_, void *p) =
                is_queue_enqueue_context(ctxt) &*& queue_enqueue_context_pre(ctxt)(info, inv, queue, value);

            lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
                requires
                    atomic_load_pointer_context_pre(context)(?info_, ?inv_, ?pp) &*&
                    inv_() &*&
                    is_atomic_load_pointer_operation(op) &*&
                    atomic_load_pointer_operation_pre(pp);
                ensures
                    atomic_load_pointer_context_post(context)(info_, ?p) &*& inv_() &*&
                    is_atomic_load_pointer_operation(op) &*&
                    atomic_load_pointer_operation_post(p);
            {
                {
                    predicate_family_instance queue_enqueue_operation_pre(enqueue_op)(unit info__, struct queue *queue_, void *value_) =
                        is_atomic_load_pointer_operation(op) &*& queue_ == queue &*& value_ == value &*&
                        atomic_load_pointer_operation_pre(&queue->last);

                    predicate_family_instance queue_enqueue_operation_post(enqueue_op)(unit info__, bool success) =
                        is_atomic_load_pointer_operation(op) &*&
                        atomic_load_pointer_operation_post(_) &*& !success;

                    lemma bool enqueue_op() : queue_enqueue_operation
                        requires queue_enqueue_operation_pre(enqueue_op)(?info__, ?queue__, ?value__) &*& queue_state(queue__, ?values);
                        ensures !result &*& queue_enqueue_operation_post(enqueue_op)(info__, false) &*& queue_state(queue__, values);
                    {
                        open queue_enqueue_operation_pre(enqueue_op)(?info___, _, _);
                        open queue_state(queue, values);
                        open queue_last(queue, _);
                        op();
                        assert pointer(&queue->last, ?last_);
                        close queue_last(queue, last_);
                        close queue_state(queue, values);
                        close queue_enqueue_operation_post(enqueue_op)(info___, false);
                        return false;
                    }

                    open atomic_load_pointer_context_pre(context)(?info___, _, _);
                    close queue_enqueue_operation_pre(enqueue_op)(unit, queue, value);
                    produce_lemma_function_pointer_chunk(enqueue_op) {
                        ctxt(enqueue_op);
                    }
                    open queue_enqueue_operation_post(enqueue_op)(_, _);
                    assert atomic_load_pointer_operation_post(?p);
                    close atomic_load_pointer_context_post(context)(info___, p);
                }
            }
            @*/
            //@ close atomic_load_pointer_context_pre(context)(unit, inv, &queue->last);
            //@ close atomic_load_pointer_ghost_arg(context);
            //@ produce_lemma_function_pointer_chunk(context);
            last = atomic_load_pointer(&queue->last);
            //@ leak is_atomic_load_pointer_context(_);
            //@ open atomic_load_pointer_context_post(context)(_, _);
        }
    
        n->next = last;
        /*@
        close
            atomic_compare_and_store_pointer_context_pre
            (queue_enqueue_atomic_compare_and_store_pointer_context)
            (queue_enqueue_atomic_compare_and_store_pointer_context_info(ctxt, info, inv, queue, value, last, n), inv, &queue->last, last, n);
        @*/
        //@ close atomic_compare_and_store_pointer_ghost_arg(queue_enqueue_atomic_compare_and_store_pointer_context);
        //@ produce_lemma_function_pointer_chunk(queue_enqueue_atomic_compare_and_store_pointer_context);
        done = atomic_compare_and_store_pointer(&queue->last, last, n);
        //@ leak is_atomic_compare_and_store_pointer_context(_);
        //@ open atomic_compare_and_store_pointer_context_post(queue_enqueue_atomic_compare_and_store_pointer_context)(_, _);
    }
}

/*@

// ***************** begin atomic_load_pointer *******************

inductive queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation_info =
    queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation_info(
        atomic_load_pointer_operation *op, struct queue *queue, struct node *middle);

predicate_family_instance queue_try_dequeue_operation_pre
    (queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation)
    (queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation_info info, struct queue *queue)
    =
    switch (info) {
        case queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation_info(op, queue_, middle):
            return
                is_atomic_load_pointer_operation(op) &*&
                atomic_load_pointer_operation_pre(&queue->last) &*&
                [1/2]queue->ghost_middle |-> middle &*&
                [1/2]queue->front_values |-> nil &*&
                queue_ == queue;
    };

predicate_family_instance queue_try_dequeue_operation_post
    (queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation)
    (queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation_info info, bool success, void *value)
    =
    switch (info) {
        case queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation_info(op, queue, middle):
            return
                is_atomic_load_pointer_operation(op) &*&
                atomic_load_pointer_operation_post(?last) &*& [1/2]queue->ghost_middle |-> last &*&
                success == (middle != last) &*&
                success ?
                    node_value(last, ?lastValue) &*&
                    [1/2]node_next(last, ?lastNext) &*&
                    malloc_block_node(last) &*&
                    lseg(lastNext, middle, ?backValuesTail) &*&
                    [1/2]middle->next |-> _ &*&
                    value == reverseHead(lastValue, backValuesTail) &*&
                    [1/2]queue->front_values |-> reverseTail(lastValue, backValuesTail)
                :
                    [1/2]queue->front_values |-> nil;
    };

lemma bool queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation() : queue_try_dequeue_operation
    requires queue_try_dequeue_operation_pre(queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation)(?info, ?queue) &*& queue_state(queue, ?values);
    ensures
        switch (values) {
            case nil: return queue_try_dequeue_operation_post(queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation)(info, false, _) &*& queue_state(queue, nil);
            case cons(h, t): return queue_try_dequeue_operation_post(queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation)(info, true, h) &*& queue_state(queue, t);
        };
{
    open queue_try_dequeue_operation_pre(queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation)(?info_, queue);
    open queue_state(queue, values);
    merge_fractions queue_front_values(queue, _);
    switch (info_) {
        case queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation_info(op, queue_, middle):
            open queue_last(queue, _);
            op();
            assert atomic_load_pointer_operation_post(?last);
            close queue_last(queue, last);
            merge_fractions queue_ghost_middle(queue, _);
            queue->ghost_middle = last;
            split_fraction queue_ghost_middle(queue, _);
            if (middle != last) {
                open lseg(last, middle, ?backValues);
                split_fraction node_next(last, _);
                assert node_value(last, ?lastValue);
                assert [_]node_next(last, ?lastNext);
                assert lseg(lastNext, middle, ?backValuesTail);
                close lseg(last, last, nil);
                queue->front_values = reverseTail(lastValue, backValuesTail);
                split_fraction queue_front_values(queue, _);
                append_nil(reverseTail(lastValue, backValuesTail));
                close queue_state(queue, reverseTail(lastValue, backValuesTail));
                close queue_try_dequeue_operation_post(queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation)(info_, true, reverseHead(lastValue, backValuesTail));
                reverse_head_tail_lemma(lastValue, backValuesTail);
            } else {
                open lseg(last, last, _);
                close lseg(last, last, nil);
                split_fraction queue_front_values(queue, _);
                close queue_state(queue, nil);
                close queue_try_dequeue_operation_post(queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation)(info_, false, 0);
            }
            return middle != last;
    }
}

inductive queue_try_dequeue_atomic_load_pointer_context_info =
  queue_try_dequeue_atomic_load_pointer_context_info(
      queue_try_dequeue_context *ctxt,
      any ctxtInfo,
      predicate() inv,
      struct queue *queue,
      struct node *middle
  );

predicate_family_instance atomic_load_pointer_context_pre
    (queue_try_dequeue_atomic_load_pointer_context)
    (queue_try_dequeue_atomic_load_pointer_context_info info, predicate() inv, void **pp) =
    switch (info) {
        case queue_try_dequeue_atomic_load_pointer_context_info(ctxt, ctxtInfo, inv_, queue, middle):
            return
                is_queue_try_dequeue_context(ctxt) &*&
                queue_try_dequeue_context_pre(ctxt)(ctxtInfo, inv, queue) &*&
                pp == &queue->last &*&
                [1/2]queue->ghost_middle |-> middle &*&
                [1/2]queue->front_values |-> nil;
    };

predicate_family_instance atomic_load_pointer_context_post
    (queue_try_dequeue_atomic_load_pointer_context)
    (queue_try_dequeue_atomic_load_pointer_context_info info, void *p) =
    switch (info) {
        case queue_try_dequeue_atomic_load_pointer_context_info(ctxt, ctxtInfo, inv, queue, middle):
            return
                is_queue_try_dequeue_context(ctxt) &*&
                [1/2]queue->ghost_middle |-> p &*&
                p == middle ?
                    queue_try_dequeue_context_post(ctxt)(ctxtInfo, false, _) &*&
                    [1/2]queue->front_values |-> nil
                :
                    node_value(p, ?lastValue) &*&
                    [1/2]node_next(p, ?lastNext) &*&
                    malloc_block_node(p) &*&
                    lseg(lastNext, middle, ?backValuesTail) &*&
                    queue_try_dequeue_context_post(ctxt)(ctxtInfo, true, reverseHead(lastValue, backValuesTail)) &*&
                    [1/2]queue->front_values |-> reverseTail(lastValue, backValuesTail) &*&
                    [1/2]middle->next |-> _;
    };

lemma void queue_try_dequeue_atomic_load_pointer_context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
    requires
        atomic_load_pointer_context_pre(queue_try_dequeue_atomic_load_pointer_context)(?info, ?inv, ?pp) &*&
        inv() &*&
        is_atomic_load_pointer_operation(op) &*&
        atomic_load_pointer_operation_pre(pp);
    ensures
        atomic_load_pointer_context_post(queue_try_dequeue_atomic_load_pointer_context)(info, ?p) &*&
        inv() &*&
        is_atomic_load_pointer_operation(op) &*&
        atomic_load_pointer_operation_post(p);
{
    open atomic_load_pointer_context_pre(queue_try_dequeue_atomic_load_pointer_context)(?info_, inv, pp);
    switch (info_) {
        case queue_try_dequeue_atomic_load_pointer_context_info(ctxt, ctxtInfo, inv_, queue, middle):
            close
                queue_try_dequeue_operation_pre
                (queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation)
                (queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation_info(op, queue, middle), queue);
            produce_lemma_function_pointer_chunk(queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation) {
              ctxt(queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation);
            }
            open
                queue_try_dequeue_operation_post
                (queue_try_dequeue_atomic_load_pointer_queue_try_dequeue_operation)
                (_, _, _);
    }
    assert atomic_load_pointer_operation_post(?p);
    close atomic_load_pointer_context_post(queue_try_dequeue_atomic_load_pointer_context)(info_, p);
}

// ***************** end atomic_load_pointer *******************

// ***************** begin atomic_noop *******************

inductive queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation_info =
    queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation_info(
        struct queue *queue,
        void *frontValuesHead,
        list<void *> frontValuesTail
    );

predicate_family_instance queue_try_dequeue_operation_pre(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation)(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation_info info, struct queue *queue) =
    switch (info) {
        case queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation_info(queue_, frontValuesHead, frontValuesTail):
            return [1/2]queue->front_values |-> cons(frontValuesHead, frontValuesTail) &*& queue == queue_;
    };
predicate_family_instance queue_try_dequeue_operation_post(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation)(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation_info info, bool result, void *value) =
    switch (info) {
        case queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation_info(queue, frontValuesHead, frontValuesTail):
            return result &*& value == frontValuesHead &*& [1/2]queue->front_values |-> frontValuesTail;
    };

lemma bool queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation() : queue_try_dequeue_operation
    requires queue_try_dequeue_operation_pre(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation)(?info, ?queue) &*& queue_state(queue, ?values);
    ensures
        switch (values) {
            case nil: return false;
            case cons(h, t):
                return queue_try_dequeue_operation_post(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation)(info, true, h) &*& queue_state(queue, t);
        };
{
    open queue_try_dequeue_operation_pre(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation)(?info_, queue);
    open queue_state(queue, values);
    merge_fractions queue_front_values(queue, ?frontValues);
    assert lseg(_, _, ?backValues);
    switch (frontValues) {
        case nil:
        case cons(h, t):
            queue->front_values = t;
            split_fraction queue_front_values(queue, _);
            close queue_state(queue, append(t, reverse(backValues)));
            close queue_try_dequeue_operation_post(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation)(info_, true, h);
            return true;
    }
}

inductive queue_try_dequeue_atomic_noop_context_info =
    queue_try_dequeue_atomic_noop_context_info(queue_try_dequeue_context *ctxt, any ctxtInfo, struct queue *queue, void *frontValuesHead, list<void *> frontValuesTail);

predicate_family_instance atomic_noop_context_pre(queue_try_dequeue_atomic_noop_context)(queue_try_dequeue_atomic_noop_context_info info, predicate() inv) =
    switch (info) {
        case queue_try_dequeue_atomic_noop_context_info(ctxt, ctxtInfo, queue, frontValuesHead, frontValuesTail):
            return is_queue_try_dequeue_context(ctxt) &*& queue_try_dequeue_context_pre(ctxt)(ctxtInfo, inv, queue) &*& [1/2]queue->front_values |-> cons(frontValuesHead, frontValuesTail);
    };
predicate_family_instance atomic_noop_context_post(queue_try_dequeue_atomic_noop_context)(queue_try_dequeue_atomic_noop_context_info info) =
    switch (info) {
        case queue_try_dequeue_atomic_noop_context_info(ctxt, ctxtInfo, queue, frontValuesHead, frontValuesTail):
            return is_queue_try_dequeue_context(ctxt) &*& queue_try_dequeue_context_post(ctxt)(ctxtInfo, true, frontValuesHead) &*& [1/2]queue->front_values |-> frontValuesTail;
    };

lemma void queue_try_dequeue_atomic_noop_context() : atomic_noop_context
    requires atomic_noop_context_pre(queue_try_dequeue_atomic_noop_context)(?info, ?inv) &*& inv();
    ensures atomic_noop_context_post(queue_try_dequeue_atomic_noop_context)(info) &*& inv();
{
    open atomic_noop_context_pre(queue_try_dequeue_atomic_noop_context)(?info_, inv);
    switch (info_) {
        case queue_try_dequeue_atomic_noop_context_info(ctxt, ctxtInfo, queue, frontValuesHead, frontValuesTail):
            close queue_try_dequeue_operation_pre(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation)(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation_info(queue, frontValuesHead, frontValuesTail), queue);
            produce_lemma_function_pointer_chunk(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation) {
              ctxt(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation);
            }
            open queue_try_dequeue_operation_post(queue_try_dequeue_atomic_noop_context_queue_try_dequeue_operation)(_, _, _);
            close atomic_noop_context_post(queue_try_dequeue_atomic_noop_context)(info_);
    }
}

// ***************** end atomic_noop *******************

@*/

bool queue_try_dequeue(struct queue *queue, void **pvalue)
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        queue_try_dequeue_context_pre(?ctxt)(?info, inv, queue) &*& is_queue_try_dequeue_context(ctxt) &*&
        queue_consumer(queue) &*& pointer(pvalue, _);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        queue_try_dequeue_context_post(ctxt)(info, result, ?value0) &*& is_queue_try_dequeue_context(ctxt) &*&
        pointer(pvalue, ?value) &*& queue_consumer(queue) &*& result ? value0 == value : true;
    @*/
{
    //@ open queue_consumer(queue);
    struct node *first = queue->first;
    struct node *middle = queue->middle;
    //@ open lseg2(first, middle, ?firstValue, ?frontValues);
    //@ close lseg2(first, middle, firstValue, frontValues);
    if (first == middle) {

        /*@
        close
            atomic_load_pointer_context_pre
            (queue_try_dequeue_atomic_load_pointer_context)
            (queue_try_dequeue_atomic_load_pointer_context_info(ctxt, info, inv, queue, middle), inv, &queue->last);
        @*/
        //@ close atomic_load_pointer_ghost_arg(queue_try_dequeue_atomic_load_pointer_context);
        //@ produce_lemma_function_pointer_chunk(queue_try_dequeue_atomic_load_pointer_context);
        struct node *last = atomic_load_pointer(&queue->last);
        //@ leak is_atomic_load_pointer_context(_);
        //@ open atomic_load_pointer_context_post(queue_try_dequeue_atomic_load_pointer_context)(_, _);
        
        if (last == middle) {
            //@ close queue_consumer(queue);
            return false;
        }
        //@ open lseg2(first, middle, _, nil);
        struct node *node = last;
        //@ assert last->value |-> ?lastValue;
        struct node *prev = last->next;
        //@ close lseg2(node, last, lastValue, nil);
        //@ assert [1/2]queue->front_values |-> ?backValuesReverseTail;
        //@ assert lseg(prev, middle, ?backValuesTail);
        //@ append_nil(backValuesReverseTail);
        //@ reverse_head_tail_lemma(lastValue, backValuesTail);
        while (prev != middle)
            //@ invariant lseg(prev, middle, ?frontBackValues) &*& lseg2(node, last, ?backBackValuesReverseHead, ?backBackValuesReverseTail) &*& cons(lastValue, backValuesTail) == append(reverse(backBackValuesReverseTail), cons(backBackValuesReverseHead, frontBackValues));
        {
            //@ open lseg(prev, middle, _);
            //@ void *prevValue = prev->value;
            struct node *prevPrev = prev->next;
            //@ assert node_value(prev, ?frontBackValuesHead) &*& lseg(prevPrev, middle, ?frontBackValuesTail);
            prev->next = node;
            //@ lseg2_distinct(node, last, prev);
            node = prev;
            prev = prevPrev;
            //@ split_fraction node_next(node, _);
            //@ close lseg2(node, last, prevValue, cons(backBackValuesReverseHead, backBackValuesReverseTail));
            //@ append_assoc(reverse(backBackValuesReverseTail), cons(backBackValuesReverseHead, nil), frontBackValues);
        }
        //@ open lseg(prev, middle, _);
        //@ merge_fractions node_next(first, _);
        first->next = node;
        //@ split_fraction node_next(first, _);
        middle = last;
        queue->middle = middle;
        //@ append_nil(reverse(cons(backBackValuesReverseHead, backBackValuesReverseTail)));
        //@ assert cons(lastValue, backValuesTail) == reverse(cons(backBackValuesReverseHead, backBackValuesReverseTail));
        //@ reverse_reverse(cons(backBackValuesReverseHead, backBackValuesReverseTail));
        //@ close lseg2(first, last, firstValue, reverse(cons(lastValue, backValuesTail)));
    } else {
        //@ open lseg2(first, middle, _, _);
        //@ assert [_]first->next |-> ?firstNext &*& lseg2(firstNext, middle, ?frontValuesHead, ?frontValuesTail);
        //@ close lseg2(first, middle, firstValue, frontValues);
        //@ close atomic_noop_context_pre(queue_try_dequeue_atomic_noop_context)(queue_try_dequeue_atomic_noop_context_info(ctxt, info, queue, frontValuesHead, frontValuesTail), inv);
        //@ close atomic_noop_ghost_arg(queue_try_dequeue_atomic_noop_context);
        //@ produce_lemma_function_pointer_chunk(queue_try_dequeue_atomic_noop_context);
        atomic_noop();
        //@ leak is_atomic_noop_context(_);
        //@ open atomic_noop_context_post(queue_try_dequeue_atomic_noop_context)(_);
    }
    //@ open lseg2(first, middle, _, _);
    //@ merge_fractions node_next(first, _);
    struct node *firstNext = first->next;
    //@ open lseg2(firstNext, middle, ?firstNextValue, ?firstNextTail);
    *pvalue = firstNext->value;
    //@ close lseg2(firstNext, middle, firstNextValue, firstNextTail);
    queue->first = firstNext;
    free(first);
    //@ close queue_consumer(queue);
    return true;
}

void queue_dispose(struct queue *queue)
    //@ requires queue_consumer(queue) &*& queue_state(queue, _);
    //@ ensures emp;
{
    //@ open queue_consumer(queue);
    //@ open queue_state(queue, _);
    //@ merge_fractions queue_ghost_middle(queue, _);
    //@ merge_fractions queue_front_values(queue, _);
    struct node *first = queue->first;
    struct node *middle = queue->middle;
    struct node *last = queue->last;
    while (first != middle)
        //@ invariant lseg2(first, middle, _, _);
    {
        //@ open lseg2(first, middle, _, _);
        //@ merge_fractions node_next(first, _);
        struct node *next = first->next;
        free(first);
        first = next;
    }
    while (last != middle)
        //@ invariant lseg(last, middle, _);
    {
        //@ open lseg(last, middle, _);
        struct node *next = last->next;
        free(last);
        last = next;
    }
    //@ open lseg(last, middle, _);
    //@ open lseg2(middle, middle, _, _);
    //@ merge_fractions node_next(middle, _);
    free(middle);
    free(queue);
}
