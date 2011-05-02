#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct stack {
    struct node *head;
};

struct stack *create_stack()
    //@ requires false;
    //@ ensures true;
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
    stack->head = 0;
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires false;
    //@ ensures true;
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
}

int stack_pop(struct stack *stack)
    //@ requires false;
    //@ ensures true;
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
}

void stack_dispose(struct stack *stack)
    //@ requires false;
    //@ ensures true;
{
    struct node *n = stack->head;
    while (n != 0)
        //@ invariant true;
    {
        struct node *next = n->next;
        free(n);
        n = next;
    }
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    int x = stack_pop(s);
    assert(x == 20);
    int y = stack_pop(s);
    assert(y == 10);
    stack_dispose(s);
    return 0;
}