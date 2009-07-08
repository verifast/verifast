#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct stack {
    struct node *head;
};

/*@
inductive list = nil | cons(int, list);

fixpoint list tail(list vs) {
    switch (vs) {
        case nil: return nil;
        case cons(h, t): return t;
    }
}

predicate nodes(struct node *head, list vs) =
    head == 0 ?
        vs == nil
    :
        head->next |-> ?next &*& head->value |-> ?value &*& nodes(next, ?tail) &*& malloc_block_node(head) &*& vs == cons(value, tail);

predicate stack(struct stack *stack, list vs) =
    stack->head |-> ?head &*& nodes(head, vs) &*& malloc_block_stack(stack);
@*/

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, nil);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
    stack->head = 0;
    //@ close nodes(0, nil);
    //@ close stack(stack, nil);
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?vs);
    //@ ensures stack(stack, cons(value, vs));
{
    //@ open stack(stack, _);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, cons(value, vs));
    //@ close stack(stack, cons(value, vs));
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack, ?vs) &*& vs != nil;
    //@ ensures switch (vs) { case nil: return false; case cons(h, t): return result == h &*& stack(stack, t); };
{
    //@ open stack(stack, _);
    struct node *head = stack->head;
    //@ open nodes(head, _);
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close stack(stack, tail(vs));
    return result;
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, _);
    //@ ensures true;
{
    //@ open stack(stack, _);
    struct node *n = stack->head;
    while (n != 0)
        //@ invariant nodes(n, _);
    {
        //@ open nodes(n, _);
        struct node *next = n->next;
        free(n);
        n = next;
    }
    //@ open nodes(0, _);
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    int v1 = stack_pop(s);
    assert(v1 == 20);
    int v2 = stack_pop(s);
    assert(v2 == 10);
    stack_dispose(s);
    return 0;
}