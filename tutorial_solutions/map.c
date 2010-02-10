#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct stack {
    struct node *head;
};

/*@

predicate nodes(struct node *node, int count) =
    node == 0 ? count == 0 : 0 < count &*& node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*& nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& 0 <= count &*& nodes(head, count);

@*/

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, 0);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
    stack->head = 0;
    //@ close nodes(0, 0);
    //@ close stack(stack, 0);
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count + 1);
{
    //@ open stack(stack, count);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, count + 1);
    //@ close stack(stack, count + 1);
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack, ?count) &*& 0 < count;
    //@ ensures stack(stack, count - 1);
{
    //@ open stack(stack, count);
    struct node *head = stack->head;
    //@ open nodes(head, count);
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close stack(stack, count - 1);
    return result;
}

//@ predicate_family int_func_data(void *f)(void *data);

typedef int int_func(void *data, int x);
    //@ requires int_func_data(this)(data);
    //@ ensures int_func_data(this)(data);

void nodes_map(struct node *n, int_func *f, void *data)
    //@ requires nodes(n, ?count) &*& is_int_func(f) == true &*& int_func_data(f)(data);
    //@ ensures nodes(n, count) &*& is_int_func(f) == true &*& int_func_data(f)(data);
{
    //@ open nodes(n, _);
    if (n != 0) {
        int y = f(data, n->value);
        n->value = y;
        nodes_map(n->next, f, data);
    }
    //@ close nodes(n, count);
}

void stack_map(struct stack *stack, int_func *f, void *data)
    //@ requires stack(stack, ?count) &*& is_int_func(f) == true &*& int_func_data(f)(data);
    //@ ensures stack(stack, count) &*& is_int_func(f) == true &*& int_func_data(f)(data);
{
    //@ open stack(stack, _);
    nodes_map(stack->head, f, data);
    //@ close stack(stack, count);
}

void nodes_dispose(struct node *n)
    //@ requires nodes(n, _);
    //@ ensures true;
{
    //@ open nodes(n, _);
    if (n != 0) {
        nodes_dispose(n->next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, _);
    //@ ensures true;
{
    //@ open stack(stack, _);
    nodes_dispose(stack->head);
    free(stack);
}

struct plus_a_data {
    int a;
};

/*@

predicate_family_instance int_func_data(plus_a)(void *data) =
    plus_a_data_a(data, _);

@*/

int plus_a(struct plus_a_data *data, int x) //@ : int_func
    //@ requires int_func_data(plus_a)(data);
    //@ ensures int_func_data(plus_a)(data);
{
    //@ open int_func_data(plus_a)(data);
    int result = x + data->a;
    //@ close int_func_data(plus_a)(data);
    return result;
}

int read_int();
    //@ requires true;
    //@ ensures true;

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    int a = read_int();
    struct plus_a_data *data = malloc(sizeof(struct plus_a_data));
    if (data == 0) abort();
    data->a = a;
    //@ close int_func_data(plus_a)(data);
    stack_map(s, plus_a, data);
    //@ open int_func_data(plus_a)(data);
    free(data);
    stack_dispose(s);
    return 0;
}
