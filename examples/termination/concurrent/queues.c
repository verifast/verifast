#include "stdlib.h"
#include "queues.h"

struct node {
    struct node *next;
    void *value;
};

/*@
predicate lseg(struct node *first, struct node *last, list<void *> values) =
    first == last ?
        values == nil
    :
        first->next |-> ?next &*& first->value |-> ?value &*&
        malloc_block_node(first) &*&
        lseg(next, last, ?values0) &*&
        values == cons(value, values0);

lemma void lseg_add(struct node *first)
    requires lseg(first, ?last, ?values) &*&
        last->next |-> ?next &*& last->value |-> ?value &*&
        malloc_block_node(last) &*&
        next->next |-> _;
    ensures lseg(first, next, append(values, cons(value, nil)))
        &*& next->next |-> _;
{
    open lseg(first, last, values);
    if (first == last) {
        close lseg(next, next, nil);
    } else {
        lseg_add(first->next);
    }
    close lseg(first, next, _);
}
@*/

struct queue {
    struct node *first;
    struct node *last;
};

/*@
predicate queue(struct queue *q, list<void *> values) =
    q->first |-> ?first &*& q->last |-> ?last &*&
    malloc_block_queue(q) &*&
    lseg(first, last, values) &*&
    last->next |-> _ &*& last->value |-> _ &*&
    malloc_block_node(last);
@*/

struct queue *create_queue()
    //@ requires true;
    //@ ensures queue(result, nil);
    //@ terminates;
{
    struct queue *q = malloc(sizeof(struct queue));
    if (q == 0) abort();
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    q->first = n;
    q->last = n;
    //@ close lseg(n, n, nil);
    //@ close queue(q, nil);
    return q;
}

void enqueue(struct queue *q, void *x)
    //@ requires queue(q, ?vs);
    //@ ensures queue(q, append(vs, {x}));
    //@ terminates;
{
    //@ open queue(q, vs);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    q->last->next = n;
    q->last->value = x;
    q->last = n;
    //@ lseg_add(q->first);
    //@ close queue(q, _);
}

void *dequeue(struct queue *q)
    //@ requires queue(q, cons(?v, ?vs));
    //@ ensures queue(q, vs) &*& result == v;
    //@ terminates;
{
    //@ open queue(q, _);
    struct node *n = q->first;
    //@ open lseg(n, _, _);
    void *result = n->value;
    q->first = n->next;
    free(n);
    //@ close queue(q, _);
    return result;
}

void queue_dispose(struct queue *q)
    //@ requires queue(q, _);
    //@ ensures true;
    //@ terminates;
{
    //@ open queue(q, _);
    struct node *n = q->first;
    struct node *last = q->last;
    while (n != last)
        //@ invariant lseg(n, last, ?vs);
        //@ decreases length(vs);
    {
        //@ open lseg(_, _, _);
        struct node *next = n->next;
        free(n);
        n = next;
    }
    //@ open lseg(n, last, _);
    free(last);
    free(q);
}
