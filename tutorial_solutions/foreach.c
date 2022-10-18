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
        values == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*&
        nodes(next, ?values0) &*& values == cons(value, values0);

predicate stack(struct stack *stack, list<void *> values) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head, values);

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

void stack_push(struct stack *stack, void *value)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, cons(value, values));
{
    //@ open stack(stack, values);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, cons(value, values));
    //@ close stack(stack, cons(value, values));
}

bool stack_is_empty(struct stack *stack)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, values) &*& result == (values == nil);
{
    //@ open stack(stack, values);
    struct node *head = stack->head;
    //@ open nodes(head, values);
    bool result = head == 0;
    //@ close nodes(head, values);
    //@ close stack(stack, values);
    return result;
}

void *stack_pop(struct stack *stack)
    //@ requires stack(stack, ?values) &*& values != nil;
    //@ ensures stack(stack, tail(values)) &*& result == head(values);
{
    //@ open stack(stack, values);
    struct node *head = stack->head;
    //@ open nodes(head, values);
    stack->head = head->next;
    void *result = head->value;
    free(head);
    //@ close stack(stack, tail(values));
    return result;
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, nil);
    //@ ensures true;
{
    //@ open stack(stack, nil);
    //@ open nodes(_, _);
    free(stack);
}

char input_char();
    //@ requires true;
    //@ ensures true;

int input_int();
    //@ requires true;
    //@ ensures true;

void output_int(int x);
    //@ requires true;
    //@ ensures true;

struct vector {
    int x;
    int y;
};

//@ predicate vector(struct vector *v) = v->x |-> ?x &*& v->y |-> ?y &*& malloc_block_vector(v);

struct vector *create_vector(int x, int y)
    //@ requires true;
    //@ ensures vector(result);
{
    struct vector *result = malloc(sizeof(struct vector));
    if (result == 0) abort();
    result->x = x;
    result->y = y;
    //@ close vector(result);
    return result;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    //@ close foreach(nil, vector);
    while (true)
        //@ invariant stack(s, ?values) &*& foreach(values, vector);
    {
        char c = input_char();
        if (c == 'p') {
            int x = input_int();
            int y = input_int();
            struct vector *v = create_vector(x, y);
            stack_push(s, v);
            //@ close foreach(cons(v, values), vector);
        } else if (c == '+') {
            bool empty = stack_is_empty(s);
            if (empty) abort();
            struct vector *v1 = stack_pop(s);
            //@ open foreach(values, vector);
            //@ open vector(head(values));
            empty = stack_is_empty(s);
            if (empty) abort();
            struct vector *v2 = stack_pop(s);
            //@ open foreach(tail(values), vector);
            //@ open vector(head(tail(values)));
            struct vector *sum = create_vector(v1->x + v2->x, v1->y + v2->y);
            free(v1);
            free(v2);
            stack_push(s, sum);
            //@ close foreach(cons(sum, tail(tail(values))), vector);
        } else if (c == '=') {
            bool empty = stack_is_empty(s);
            if (empty) abort();
            struct vector *v = stack_pop(s);
            //@ open foreach(values, vector);
            //@ open vector(head(values));
            output_int(v->x);
            output_int(v->y);
            free(v);
        } else {
            abort();
        }
    }
}