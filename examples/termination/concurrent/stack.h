#ifndef STACK_H
#define STACK_H

struct stack;
typedef struct stack *stack;

//@ predicate stack(stack stack; predicate(void *) p);

stack create_stack();
    //@ requires exists<predicate(void *)>(?p);
    //@ ensures [_]stack(result, p); 
    //@ terminates;

void stack_push(stack stack, void *value);
    //@ requires [_]stack(stack, ?p) &*& p(value);
    //@ ensures true;
    //@ terminates;

bool stack_pop(stack stack, void **pvalue);
    //@ requires [_]stack(stack, ?p) &*& *pvalue |-> _;
    //@ ensures *pvalue |-> ?value &*& result ? p(value) : true;
    //@ terminates;

#endif
