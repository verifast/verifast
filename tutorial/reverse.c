#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct stack {
    struct node *head;
};

/*@

inductive ints = ints_nil | ints_cons(int, ints);

fixpoint int ints_head(ints values) {
    switch (values) {
        case ints_nil: return 0;
        case ints_cons(value, values0): return value;
    }
}

fixpoint ints ints_tail(ints values) {
    switch (values) {
        case ints_nil: return ints_nil;
        case ints_cons(value, values0): return values0;
    }
}

predicate nodes(struct node *node, ints values) =
    node == 0 ?
        values == ints_nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*&
        nodes(next, ?values0) &*& values == ints_cons(value, values0);

predicate stack(struct stack *stack, ints values) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head, values);

@*/

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, ints_nil);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
    stack->head = 0;
    //@ close nodes(0, ints_nil);
    //@ close stack(stack, ints_nil);
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, ints_cons(value, values));
{
    //@ open stack(stack, values);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, ints_cons(value, values));
    //@ close stack(stack, ints_cons(value, values));
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack, ?values) &*& values != ints_nil;
    //@ ensures stack(stack, ints_tail(values)) &*& result == ints_head(values);
{
    //@ open stack(stack, values);
    struct node *head = stack->head;
    //@ open nodes(head, values);
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close stack(stack, ints_tail(values));
    return result;
}

/*@

fixpoint ints ints_append(ints values1, ints values2) {
    switch (values1) {
        case ints_nil: return values2;
        case ints_cons(h, t): return ints_cons(h, ints_append(t, values2));
    }
}

lemma void ints_append_nil_lemma(ints values)
    requires true;
    ensures ints_append(values, ints_nil) == values;
{
    switch (values) {
        case ints_nil:
        case ints_cons(h, t):
            ints_append_nil_lemma(t);
    }
}

lemma void ints_append_assoc_lemma(ints values1, ints values2, ints values3)
    requires true;
    ensures ints_append(ints_append(values1, values2), values3) == ints_append(values1, ints_append(values2, values3));
{
    switch (values1) {
        case ints_nil:
        case ints_cons(h, t):
            ints_append_assoc_lemma(t, values2, values3);
    }
}

fixpoint ints ints_reverse(ints values) {
    switch (values) {
        case ints_nil: return ints_nil;
        case ints_cons(h, t): return ints_append(ints_reverse(t), ints_cons(h, ints_nil));
    }
}

@*/

void stack_reverse(struct stack *stack)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, ints_reverse(values));
{
    //@ open stack(stack, values);
    struct node *n = stack->head;
    struct node *m = 0;
    //@ close nodes(m, ints_nil);
    //@ ints_append_nil_lemma(ints_reverse(values));
    while (n != 0)
        //@ invariant nodes(m, ?values1) &*& nodes(n, ?values2) &*& ints_reverse(values) == ints_append(ints_reverse(values2), values1);
    {
        //@ open nodes(n, values2);
        struct node *next = n->next;
        //@ assert nodes(next, ?values2tail) &*& n->value |-> ?value;
        n->next = m;
        m = n;
        n = next;
        //@ close nodes(m, ints_cons(value, values1));
        //@ ints_append_assoc_lemma(ints_reverse(values2tail), ints_cons(value, ints_nil), values1);
    }
    //@ open nodes(n, _);
    stack->head = m;
    //@ close stack(stack, ints_reverse(values));
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, ints_nil);
    //@ ensures true;
{
    //@ open stack(stack, ints_nil);
    //@ open nodes(_, _);
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    int result1 = stack_pop(s);
    assert(result1 == 20);
    int result2 = stack_pop(s);
    assert(result2 == 10);
    stack_dispose(s);
    return 0;
}