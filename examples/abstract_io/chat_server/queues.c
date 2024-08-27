#include <stdlib.h>
#include "queues.h"

typedef struct node {
    struct node *next;
    void *value;
} *node;

/*@

predicate nodes<t>(node first, node last, predicate(void *; t) pred; list<t> elems) =
    first == last ?
        elems == nil
    :
        first->next |-> ?next &*& first->value |-> ?value &*& pred(value, ?elem) &*& malloc_block_node(first) &*&
        nodes(next, last, pred, ?elems0) &*& elems == cons(elem, elems0);

lemma void nodes_add<t>()
    requires nodes<t>(?first, ?last, ?pred, ?elems) &*& last->next |-> ?next &*& last->value |-> ?value &*& pred(value, ?elem) &*& malloc_block_node(last) &*& next->next |-> _;
    ensures nodes<t>(first, next, pred, append(elems, {elem})) &*& next->next |-> _;
{
    open nodes(first, last, pred, elems);
    if (first == last) {
        close nodes(next, next, pred, nil);
        close nodes(last, next, pred, {elem});
    } else {
        nodes_add();
        close nodes(first, next, pred, append(elems, {elem}));
    }
}
    
@*/

struct queue {
    node first;
    node last; // A sentinel node
};

/*@

predicate queue<t>(queue queue, predicate(void *; t) pred; list<t> elems) =
    queue->first |-> ?first &*& queue->last |-> ?last &*& malloc_block_queue(queue) &*&
    nodes(first, last, pred, elems) &*& last->next |-> _ &*& last->value |-> _ &*& malloc_block_node(last);

@*/

queue create_queue/*@ <t> @*/()
    //@ requires create_queue_ghost_args<t>(?pred);
    //@ ensures queue(result, pred, nil);
{
    //@ open create_queue_ghost_args(_);
    queue result = malloc(sizeof(struct queue));
    if (result == 0) abort();
    node sentinel = malloc(sizeof(struct node));
    if (sentinel == 0) abort();
    result->first = sentinel;
    result->last = sentinel;
    //@ close nodes(sentinel, sentinel, pred, nil);
    //@ close queue(result, pred, nil);
    return result;
}

void queue_enqueue/*@ <t> @*/(queue queue, void *elem)
    //@ requires queue<t>(queue, ?pred, ?elems) &*& pred(elem, ?v);
    //@ ensures queue<t>(queue, pred, append(elems, {v}));
{
    node sentinel = malloc(sizeof(struct node));
    if (sentinel == 0) abort();
    queue->last->next = sentinel;
    queue->last->value = elem;
    //@ nodes_add();
    queue->last = sentinel;
    //@ close queue(queue, pred, append(elems, {v}));
}

bool queue_is_empty/*@ <t> @*/(queue queue)
    //@ requires [?f]queue<t>(queue, ?pred, ?elems);
    //@ ensures [f]queue<t>(queue, pred, elems) &*& result == (elems == nil);
{
    //@ open queue(queue, pred, elems);
    //@ open nodes(?first, ?last, _, _);
    //@ if ((uintptr_t)queue->first == (uintptr_t)queue->last && queue->first != queue->last) { pointer__fractions_same_address(&queue->first->next, &queue->last->next); }
    //@ close [f]nodes(first, last, pred, elems);
    return queue->first == queue->last;
    //@ close [f]queue(queue, pred, elems);
}

void *queue_dequeue/*@ <t> @*/(queue queue)
    //@ requires queue<t>(queue, ?pred, cons(?v, ?elems));
    //@ ensures queue<t>(queue, pred, elems) &*& pred(result, v);
{
    //@ open queue(queue, pred, _);
    //@ open nodes(_, _, _, _);
    node first = queue->first;
    queue->first = first->next;
    void *result = first->value;
    free(first);
    //@ close queue(queue, pred, elems);
    return result;
}

#endif
