#include "stdlib.h"
#include "atomics.h"
//@ #include "listex.gh"
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
        assert [1/2]first->next |-> ?next;
        lseg2_distinct(next, middle, n);
        split_fraction node_next(first, _);
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

void queue_enqueue(struct queue *queue, void *value)
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
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->value = value;
    bool done = false;
    while (!done)
        //@ invariant is_queue_enqueue_context(ctxt, inv, queue, value, pre, post) &*& [f]atomic_space(inv) &*& (done ? post() : n->next |-> _ &*& n->value |-> value &*& malloc_block_node(n) &*& pre());
    {
        struct node *last = 0;
        {
            /*@
            predicate pre_() = is_queue_enqueue_context(ctxt, inv, queue, value, pre, post) &*& pre();
            predicate post_(void *value_) = is_queue_enqueue_context(ctxt, inv, queue, value, pre, post) &*& pre();
            @*/
            /*@
            produce_lemma_function_pointer_chunk atomic_load_pointer_context(inv, &queue->last, pre_, post_)() {
                assert is_atomic_load_pointer_operation(?op, _, ?P, ?Q);
                open pre_();
                {
                    predicate pre__() = is_atomic_load_pointer_operation(op, &queue->last, P, Q) &*& P();
                    predicate post__(bool result) = is_atomic_load_pointer_operation(op, &queue->last, P, Q) &*& Q(_) &*& result == false;
                    produce_lemma_function_pointer_chunk queue_enqueue_operation(queue, value, pre__, post__)() {
                        open pre__();
                        open queue_state(queue, ?values);
                        op();
                        close queue_state(queue, values);
                        close post__(false);
                    } {
                        close pre__();
                        ctxt();
                        open post__(_);
                    }
                }
                assert Q(?value_);
                close post_(value_);
            };
            @*/
            //@ close pre_();
            last = atomic_load_pointer(&queue->last);
            //@ leak is_atomic_load_pointer_context(_, _, _, _, _);
            //@ open post_(_);
        }
    
        n->next = last;
        {
            /*@
            predicate pre_() = is_queue_enqueue_context(ctxt, inv, queue, value, pre, post) &*& pre() &*& n->value |-> value &*& n->next |-> last &*& malloc_block_node(n);
            predicate post_(bool result) = is_queue_enqueue_context(ctxt, inv, queue, value, pre, post) &*& result ? post() : pre() &*& n->value |-> value &*& n->next |-> last &*& malloc_block_node(n);
            @*/
            /*@
            produce_lemma_function_pointer_chunk atomic_compare_and_store_pointer_context(inv, &queue->last, last, n, pre_, post_)() {
                assert is_atomic_compare_and_store_pointer_operation(?op, _, _, _, ?P, ?Q);
                open pre_();
                {
                    predicate pre__() = is_atomic_compare_and_store_pointer_operation(op, &queue->last, last, n, P, Q) &*& P() &*& n->value |-> value &*& n->next |-> last &*& malloc_block_node(n);
                    predicate post__(bool result) = is_atomic_compare_and_store_pointer_operation(op, &queue->last, last, n, P, Q) &*& Q(result) &*& result ? true : n->value |-> value &*& n->next |-> last &*& malloc_block_node(n);
                    produce_lemma_function_pointer_chunk queue_enqueue_operation(queue, value, pre__, post__)() {
                        open pre__();
                        open queue_state(queue, ?values);
                        bool result = op();
                        if (result) {
                            assert lseg(last, ?middle, ?backValues);
                            close lseg(n, middle, cons(value, backValues));
                            append_assoc(queue->front_values, reverse(backValues), {value});
                            close queue_state(queue, append(values, {value}));
                        } else {
                            close queue_state(queue, values);
                        }
                        close post__(result);
                    } {
                        close pre__();
                        ctxt();
                        open post__(?result);
                    };
                }
                assert Q(?result);
                close post_(result);
            };
            @*/
            //@ close pre_();
            done = atomic_compare_and_store_pointer(&queue->last, last, n);
            //@ leak is_atomic_compare_and_store_pointer_context(_, _, _, _, _, _, _);
            //@ open post_(done);
        }
    }
}

bool queue_try_dequeue(struct queue *queue, void **pvalue)
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
{
    //@ open queue_consumer(queue);
    struct node *first = queue->first;
    struct node *middle = queue->middle;
    //@ open lseg2(first, middle, ?firstValue, ?frontValues);
    //@ close lseg2(first, middle, firstValue, frontValues);
    if (first == middle) {
        struct node *last;
        {
            /*@
            predicate pre_() =
                is_queue_try_dequeue_context(ctxt, inv, queue, pre, post) &*& pre() &*&
                [1/2]queue->ghost_middle |-> middle &*& [1/2]queue->front_values |-> frontValues;
            predicate post_(void *last__) =
                is_queue_try_dequeue_context(ctxt, inv, queue, pre, post) &*&
                [1/2]queue->ghost_middle |-> ?last_ &*& last_ == last__ &*&
                post(last_ != middle, ?value) &*&
                last_ != middle ?
                    last_->value |-> ?lastValue &*& [1/2]last_->next |-> ?lastNext &*& malloc_block_node(last_) &*& lseg(lastNext, middle, ?backValues1) &*&
                    [1/2]queue->front_values |-> tail(reverse(cons(lastValue, backValues1))) &*& value == head(reverse(cons(lastValue, backValues1))) &*&
                    [1/2]middle->next |-> _
                :
                    [1/2]queue->front_values |-> nil;
            @*/
            /*@
            produce_lemma_function_pointer_chunk atomic_load_pointer_context(inv, &queue->last, pre_, post_)() {
                assert is_atomic_load_pointer_operation(?op, &queue->last, ?P, ?Q);
                open pre_();
                {
                    predicate pre__() =
                        is_atomic_load_pointer_operation(op, &queue->last, P, Q) &*& P() &*&
                        [1/2]queue->ghost_middle |-> middle &*& [1/2]queue->front_values |-> frontValues;
                    predicate post__(bool result, void *value) =
                        is_atomic_load_pointer_operation(op, &queue->last, P, Q) &*& Q(?last__) &*& {(struct node *)last__} == cons(?last_, nil) &*&
                        result == (middle != last_) &*&
                        [1/2]queue->ghost_middle |-> last_ &*&
                        result ?
                            last_->value |-> ?lastValue &*& [1/2]last_->next |-> ?lastNext &*& malloc_block_node(last_) &*& lseg(lastNext, middle, ?backValues1) &*&
                            [1/2]queue->front_values |-> tail(reverse(cons(lastValue, backValues1))) &*& value == head(reverse(cons(lastValue, backValues1))) &*&
                            [1/2]middle->next |-> _
                        :
                            [1/2]queue->front_values |-> nil;
                    produce_lemma_function_pointer_chunk queue_try_dequeue_operation(queue, pre__, post__)() {
                        open pre__();
                        open queue_state(queue, ?values);
                        op();
                        assert queue->last |-> ?last_ &*& lseg(last_, middle, ?backValues);
                        if (queue->last == middle) {
                            open lseg(last_, middle, backValues);
                            close post__(last_ != middle, head(reverse(backValues)));
                            close lseg(last_, last_, nil);
                            close queue_state(queue, nil);
                        } else {
                            queue->ghost_middle = last_;
                            queue->front_values = tail(reverse(backValues));
                            open lseg(last_, middle, backValues);
                            close post__(last_ != middle, head(reverse(backValues)));
                            close lseg(last_, last_, nil);
                            close queue_state(queue, tail(reverse(backValues)));
                        }
                    } {
                        close pre__();
                        ctxt();
                        open post__(?result, ?value);
                    }
                }
                assert Q(?last__);
                close post_(last__);
            };
            @*/
            //@ close pre_();
            last = atomic_load_pointer(&queue->last);
            //@ leak is_atomic_load_pointer_context(_, _, _, _, _);
            //@ open post_(last);
        }
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
        //@ assert [1/2]first->next |-> ?firstNext &*& lseg2(firstNext, middle, ?frontValuesHead, ?frontValuesTail);
        //@ close lseg2(first, middle, firstValue, frontValues);
        {
            /*@
            predicate pre_() =
                 is_queue_try_dequeue_context(ctxt, inv, queue, pre, post) &*& pre() &*& [1/2]queue->front_values |-> frontValues;
            predicate post_() =
                 is_queue_try_dequeue_context(ctxt, inv, queue, pre, post) &*& post(true, frontValuesHead) &*& [1/2]queue->front_values |-> frontValuesTail;
            @*/
            /*@
            produce_lemma_function_pointer_chunk atomic_noop_context(inv, pre_, post_)() {
                open pre_();
                {
                    predicate pre__() = [1/2]queue->front_values |-> frontValues;
                    predicate post__(bool result, void *value) = [1/2]queue->front_values |-> frontValuesTail &*& result == true &*& value == frontValuesHead;
                    produce_lemma_function_pointer_chunk queue_try_dequeue_operation(queue, pre__, post__)() {
                        open queue_state(queue, ?values);
                        open pre__();
                        queue->front_values = frontValuesTail;
                        close post__(true, frontValuesHead);
                        close queue_state(queue, tail(values));
                    } {
                        close pre__();
                        ctxt();
                        open post__(_, _);
                    }
                }
                close post_();
            };
            @*/
            //@ close pre_();
            atomic_noop();
            //@ leak is_atomic_noop_context(_, _, _, _);
            //@ open post_();
        }
    }
    //@ open lseg2(first, middle, _, _);
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
    struct node *first = queue->first;
    struct node *middle = queue->middle;
    struct node *last = queue->last;
    while (first != middle)
        //@ invariant lseg2(first, middle, _, _);
    {
        //@ open lseg2(first, middle, _, _);
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
    free(middle);
    free(queue);
}
