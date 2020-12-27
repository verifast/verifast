#include "stdlib.h"

struct node {
    struct node *next;
    void *value;
};

struct stack {
    struct node *head;
};

/*@

predicate nodes(struct node *node, list<void *> values) =
    node == 0 ?
        values == nil<void *>
    :
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*&
        nodes(next, ?values0) &*& values == cons<void *>(value, values0);

predicate stack(struct stack *stack, list<void *> values) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head, values);

@*/

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, nil<void *>);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
    stack->head = 0;
    //@ close nodes(0, nil<void *>);
    //@ close stack(stack, nil<void *>);
    return stack;
}

void stack_push(struct stack *stack, void *value)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, cons<void *>(value, values));
{
    //@ open stack(stack, values);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, cons<void *>(value, values));
    //@ close stack(stack, cons<void *>(value, values));
}

void stack_reverse(struct stack *stack)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, reverse<void *>(values));
{
    //@ open stack(stack, values);
    struct node *n = stack->head;
    struct node *m = 0;
    //@ close nodes(m, nil<void *>);
    //@ append_nil<void *>(reverse<void *>(values));
    while (n != 0)
        //@ invariant nodes(m, ?values1) &*& nodes(n, ?values2) &*& reverse<void *>(values) == append<void *>(reverse<void *>(values2), values1);
    {
        //@ open nodes(n, values2);
        struct node *next = n->next;
        //@ assert nodes(next, ?values2tail) &*& n->value |-> ?value;
        n->next = m;
        m = n;
        n = next;
        //@ close nodes(m, cons<void *>(value, values1));
        //@ append_assoc<void *>(reverse<void *>(values2tail), cons<void *>(value, nil<void *>), values1);
    }
    //@ open nodes(n, _);
    stack->head = m;
    //@ close stack(stack, reverse<void *>(values));
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, nil<void *>);
    //@ ensures true;
{
    //@ open stack(stack, nil<void *>);
    //@ open nodes(_, _);
    free(stack);
}

struct point {
    int x;
    int y;
};

struct point *create_point(int x, int y)
    //@ requires true;
    //@ ensures result->x |-> x &*& result->y |-> y &*& malloc_block_point(result);
{
    struct point *result = malloc(sizeof(struct point));
    if (result == 0) abort();
    result->x = x;
    result->y = y;
    return result;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    struct point *p1 = create_point(10, 0);
    struct point *p2 = create_point(0, 10);
    stack_push(s, p1);
    stack_push(s, p2);
    stack_reverse(s);
    abort();
}