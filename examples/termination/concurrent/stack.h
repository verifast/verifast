#ifndef STACK_H
#define STACK_H

//@ #include "../call_perms.gh"

struct stack;
typedef struct stack *stack;

//@ predicate stack(int callPermScope, stack stack; predicate(void *) p);

stack create_stack();
    //@ requires exists<predicate(void *)>(?p);
    //@ ensures [_]stack(call_perm_scope_of(currentThread), result, p); 
    //@ terminates;

void stack_push(stack stack, void *value);
    //@ requires [_]stack(call_perm_scope_of(currentThread), stack, ?p) &*& p(value);
    //@ ensures true;
    //@ terminates;

bool stack_pop(stack stack, void **pvalue);
    //@ requires [_]stack(call_perm_scope_of(currentThread), stack, ?p) &*& *pvalue |-> _;
    //@ ensures pointer_(pvalue, ?value_opt) &*& result ? value_opt == some(?value) &*& p(value) : true;
    //@ terminates;

#endif
