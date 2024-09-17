#include "stdlib.h"

/*@
inductive ilist = inil | icons(int, ilist);

fixpoint ilist iappend(ilist xs, ilist ys) {
    switch (xs) {
        case inil: return ys;
        case icons(h, t): return icons(h, iappend(t, ys));
    }
}
@*/

struct node {
    struct node *next;
    int value;
};

/*@
predicate lseg(struct node *first, struct node *last, ilist values) =
    first == last ?
        values == inil
    :
        first->next |-> ?next &*& first->value |-> ?value &*&
        malloc_block_node(first) &*&
        lseg(next, last, ?values0) &*&
        values == icons(value, values0);

lemma void lseg_add(struct node *first)
    requires lseg(first, ?last, ?values) &*&
        last->next |-> ?next &*& last->value |-> ?value &*&
        malloc_block_node(last) &*&
        next->next |-> _;
    ensures lseg(first, next, iappend(values, icons(value, inil)))
        &*& next->next |-> _;
{
    open lseg(first, last, values);
    if (first == last) {
        close lseg(next, next, inil);
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
predicate queue(struct queue *q, ilist values) =
    q->first |-> ?first &*& q->last |-> ?last &*&
    malloc_block_queue(q) &*&
    lseg(first, last, values) &*&
    last->next |-> _ &*& last->value |-> _ &*&
    malloc_block_node(last);
@*/

struct queue *create()
    //@ requires true;
    //@ ensures queue(result, inil);
{
    struct queue *q = malloc(sizeof(struct queue));
    if (q == 0) abort();
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    q->first = n;
    q->last = n;
    //@ close lseg(n, n, inil);
    //@ close queue(q, inil);
    return q;
}

void enqueue(struct queue *q, int x)
    //@ requires queue(q, ?vs);
    //@ ensures queue(q, iappend(vs, icons(x, inil)));
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

int dequeue(struct queue *q)
    //@ requires queue(q, ?vs) &*& vs != inil;
    //@ ensures queue(q, ?vs0) &*& vs == icons(result, vs0);
{
    //@ open queue(q, _);
    struct node *n = q->first;
    //@ open lseg(n, _, _);
    int result = n->value;
    q->first = n->next;
    free(n);
    //@ close queue(q, _);
    return result;
}

void dispose(struct queue *q)
    //@ requires queue(q, inil);
    //@ ensures true;
{
    //@ open queue(q, inil);
    //@ open lseg(_, _, _);
    free(q->first);
    free(q);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct queue *q = create();
    enqueue(q, 10);
    enqueue(q, 20);
    int x1 = dequeue(q);
    assert(x1 == 10);
    int x2 = dequeue(q);
    assert(x2 == 20);
    dispose(q);
    return 0;
}
