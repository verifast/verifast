#include "stdlib.h"
#include "atomics.h"

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
};

/*@

predicate lseg(struct node *first, struct node *last)
    requires first == last ? emp : first->next |-> ?next &*& first->value |-> _ &*& malloc_block_node(first) &*& first != 0 &*& lseg(next, last);

predicate lseg2(struct node *first, struct node *middle) =
    first->value |-> _ &*& malloc_block_node(first) &*& [1/2]first->next |-> ?next &*&
    (first == middle ? emp : [1/2]first->next |-> next &*& lseg2(next, middle));

lemma void lseg2_distinct(struct node *first, struct node *middle, struct node *n)
    requires lseg2(first, middle) &*& n->next |-> ?nNext;
    ensures lseg2(first, middle) &*& n->next |-> nNext &*& n != middle;
{
    open lseg2(first, middle);
    if (first != middle) {
        assert [_]first->next |-> ?next;
        lseg2_distinct(next, middle, n);
    }
    close lseg2(first, middle);
}

box_class queue_box(struct queue *queue, handle consumer)
{
    invariant queue->last |-> ?last &*& lseg(last, ?middle) &*& [1/2]middle->next |-> _;
    
    action produce();
        requires true;
        ensures middle == old_middle && consumer == old_consumer;
    
    action consume();
        requires actionHandle == consumer;
        ensures true;
    
    handle_predicate consumer_handle(struct node *middle0) {
        invariant middle == middle0 && consumer == predicateHandle;
        
        preserved_by produce() {}
        preserved_by consume() {}
    }
}

predicate queue_producer(struct queue *queue, box queueBox)
    requires [1/2]queue_box(queueBox, queue, _);

predicate queue_consumer(struct queue *queue, box queueBox)
    requires
        queue->first |-> ?first &*& queue->middle |-> ?middle &*& malloc_block_queue(queue)
        &*& consumer_handle(?h, queueBox, middle) &*& [1/2]queue_box(queueBox, queue, h)
        &*& lseg2(first, middle);

@*/

struct queue *create_queue()
    //@ requires emp;
    //@ ensures queue_producer(result, ?queueBox) &*& queue_consumer(result, queueBox);
{
    struct node *middle = malloc(sizeof(struct node));
    if (middle == 0) { abort(); }
    struct queue *queue = malloc(sizeof(struct queue));
    if (queue == 0) { abort(); }
    queue->first = middle;
    queue->middle = middle;
    queue->last = middle;
    //@ close lseg(middle, middle);
    //@ split_fraction node_next(middle, _);
    /*@
    create_box queueBox = queue_box(queue, consumerHandle)
    and_handle consumerHandle = consumer_handle(middle);
    @*/
    //@ split_fraction queue_box(queueBox, _, _);
    //@ close queue_producer(queue, queueBox);
    //@ close lseg2(middle, middle);
    //@ close queue_consumer(queue, queueBox);
    return queue;
}

void queue_enqueue(struct queue *queue, void *value)
    //@ requires [?f]queue_producer(queue, ?queueBox);
    //@ ensures [f]queue_producer(queue, queueBox);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->value = value;
    bool done = false;
    while (!done)
        //@ invariant [f]queue_producer(queue, queueBox) &*& (done ? emp : n->next |-> _ &*& n->value |-> _ &*& malloc_block_node(n));
    {
        //@ open queue_producer(queue, queueBox);
        //@ handle h = create_handle queue_box_handle(queueBox);
        /*@
        consuming_box_predicate queue_box(queueBox, queue, ?consumer)
        consuming_handle_predicate queue_box_handle(h)
        perform_action produce() atomic
        {
            open queue_last(queue, _);
            @*/ struct node *last = atomic_load_pointer(&queue->last); /*@
            close queue_last(queue, last);
        }
        producing_handle_predicate queue_box_handle();
        @*/
        n->next = last;
        /*@
        consuming_box_predicate queue_box(queueBox, queue, consumer)
        consuming_handle_predicate queue_box_handle(h)
        perform_action produce() atomic
        {
            open queue_last(queue, _);
            @*/ done = atomic_compare_and_store_pointer(&queue->last, last, n); /*@
            assert pointer(&queue->last, ?last2);
            close queue_last(queue, last2);
            if (done) {
                assert lseg(last, ?middle);
                close lseg(n, middle);
            }
        }
        producing_handle_predicate queue_box_handle();
        @*/
        //@ leak queue_box_handle(h, queueBox);
        //@ close [f]queue_producer(queue, queueBox);
    }
}

bool queue_try_dequeue(struct queue *queue, void **value)
    //@ requires queue_consumer(queue, ?queueBox) &*& pointer(value, _);
    //@ ensures queue_consumer(queue, queueBox) &*& pointer(value, _);
{
    //@ open queue_consumer(queue, queueBox);
    struct node *first = queue->first;
    struct node *middle = queue->middle;
    if (first == middle) {
        /*@
        consuming_box_predicate queue_box(queueBox, queue, ?consumer)
        consuming_handle_predicate consumer_handle(?consumerHandle, middle)
        perform_action consume() atomic
        {
            open queue_last(queue, _);
            @*/ struct node *last = atomic_load_pointer(&queue->last); /*@
            close queue_last(queue, last);
            if (last != middle) {
                open lseg(last, middle);
                split_fraction node_next(last, ?lastNext);
                close lseg(last, last);
            }
        }
        producing_handle_predicate consumer_handle(last);
        @*/
        if (last == middle) {
            //@ close queue_consumer(queue, queueBox);
            return false;
        }
        //@ open lseg2(first, middle);
        struct node *node = last;
        struct node *prev = last->next;
        //@ close lseg2(node, last);
        while (prev != middle)
            //@ invariant lseg(prev, middle) &*& lseg2(node, last);
        {
            //@ open lseg(prev, middle);
            struct node *prevPrev = prev->next;
            prev->next = node;
            //@ lseg2_distinct(node, last, prev);
            node = prev;
            prev = prevPrev;
            //@ split_fraction node_next(node, _);
            //@ close lseg2(node, last);
        }
        //@ open lseg(prev, middle);
        //@ merge_fractions node_next(first, _);
        first->next = node;
        //@ split_fraction node_next(first, _);
        middle = last;
        queue->middle = middle;
        //@ close lseg2(first, last);
    }
    //@ open lseg2(first, middle);
    //@ merge_fractions node_next(first, _);
    struct node *firstNext = first->next;
    //@ open lseg2(firstNext, middle);
    *value = firstNext->value;
    //@ close lseg2(firstNext, middle);
    queue->first = firstNext;
    free(first);
    //@ close queue_consumer(queue, queueBox);
    return true;
}

void queue_dispose(struct queue *queue)
    //@ requires queue_consumer(queue, ?queueBox) &*& queue_producer(queue, queueBox);
    //@ ensures emp;
{
    //@ open queue_consumer(queue, queueBox);
    //@ open queue_producer(queue, queueBox);
    //@ merge_fractions queue_box(queueBox, queue, ?consumer);
    /*@
    dispose_box queue_box(queueBox, queue, consumer)
    and_handle consumer_handle(_, _);
    @*/
    struct node *first = queue->first;
    struct node *middle = queue->middle;
    struct node *last = queue->last;
    while (first != middle)
        //@ invariant lseg2(first, middle);
    {
        //@ open lseg2(first, middle);
        //@ merge_fractions node_next(first, _);
        struct node *next = first->next;
        free(first);
        first = next;
    }
    while (last != middle)
        //@ invariant lseg(last, middle);
    {
        //@ open lseg(last, middle);
        struct node *next = last->next;
        free(last);
        last = next;
    }
    //@ open lseg(last, middle);
    //@ open lseg2(middle, middle);
    //@ merge_fractions node_next(middle, _);
    free(middle);
    free(queue);
}
