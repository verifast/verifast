#ifndef STACK_LEAKING_H
#define STACK_LEAKING_H

#include "atomics.h"

/*

A lock-free stack which allows multiple concurrent push and pop operations.
This implentations only works correctly when an external garbage collector
frees the nodes. 

The specifications show memory safety. Since the implementation assumes 
an external garbage collector, leaking nodes is allowed. The specifications 
also prove linearisability. 

When the pop operation reads the next field of the head node, there is 
a potential access hazard. The specifications release a dummy fraction 
of the head node to prevent this.

When the pop operations performs a CAS operation on the head field there
is an ABA hazard. Another thread may have popped the head node, inserted
new nodes and inserted the head node again. However, since the operation
already has a fraction of the head node before performing the CAS operation,
the next field cannot change and the pop operation completes on the 
updated stack. So, releasing a fraction of the head node is sufficient to
prove linearisability.

*/

struct stack;

/*@

predicate stack(struct stack *stack; list<void*> elems);


predicate_family stack_sep(void *sep)(any info, struct stack *stack, predicate() inv, stack_unsep *unsep);
predicate_family stack_unsep(void *unsep)(any info, struct stack *stack, predicate() inv, stack_sep *sep, list<void*> elems);

typedef lemma void stack_sep();
    requires stack_sep(this)(?info, ?stack, ?inv, ?unsep) &*& inv();
    ensures stack_unsep(unsep)(info, stack, inv, this, ?elems) &*& stack(stack, elems);

typedef lemma void stack_unsep();
    requires stack_unsep(this)(?info, ?stack, ?inv, ?sep, ?elems) &*& stack(stack, elems);
    ensures stack_sep(sep)(info, stack, inv, this) &*& inv();

predicate stack_inv_info(any info, struct stack *stack, predicate() inv, stack_sep* sep, stack_unsep* unsep);

@*/

// creating and disposing stacks

struct stack *create_stack();
    //@ requires true;
    //@ ensures stack(result, nil);

void dispose_stack(struct stack *stack);
    //@ requires stack(stack, nil);
    //@ ensures true;

// sequential operations on stacks

void stack_push_sequential(struct stack *stack, void *data);
    //@ requires stack(stack, ?elems);
    //@ ensures stack(stack, cons(data, elems));

bool stack_try_pop_sequential(struct stack *stack, void** resultRef);
    //@ requires stack(stack, ?elems) &*& pointer(resultRef, _);
    //@ ensures stack(stack, tail(elems)) &*& pointer(resultRef, head_or(elems, 0)) &*& result == (elems != nil);

// lemma's to share and unshare stacks 
/*@

lemma void share_stack(struct stack *stack);
    requires 
        stack(stack, ?elems) &*&
        is_stack_sep(?sep) &*&
        is_stack_unsep(?unsep) &*&
        stack_unsep(unsep)(?info, stack, ?inv, sep, elems);
    ensures atomic_space(inv) &*& stack_inv_info(info, stack, inv, sep, unsep);

lemma void unshare_stack(struct stack *stack);
    requires atomic_space(?inv) &*& stack_inv_info(?info, stack, inv, ?sep, ?unsep); 
    ensures stack(stack, ?elems) &*&
        is_stack_sep(sep) &*&
        is_stack_unsep(unsep) &*&
        stack_unsep(unsep)(info, stack, inv, sep, elems);

@*/

// concurrent operations on stacks

/* 
    Some notes about the following definition:
    
    The stack_push_operation lemma specifies to the client how the operation changes the stack, 
    while making abstraction of the internal state of the stack. From this specification, 
    the client of the stack can deduce how the content of the stack changes.
    This allows the client to update its invariants about the content of the stack.
    
    The stack_push_operation_* predicates are instantiated in the implementation of 
    the stack. This allows the implementation to pass in the necessary state to perform 
    the operation and show how this state is updated by the operation.
    The stack_push_operation lemma is also instantiated by the implementation and proves
    that the implementation performs the operation correctly, while updating its state.
    
    The stack_push_context lemma specifies how the operation updates the invariant of the client 
    while maintaining abstraction of the internal state of the stack. The implementation uses 
    this lemma to update the invariant of the client without knowing it.
    
    The stack_push_context_* predicates are instantiated by the clients of the stack. 
    This allows the clients to specify the state it requires to update the invariant and
    the state it releases after updating the invariant.
    The stack_push_context lemma is also instantiated by the client and proves
    that the invariant of the client is updated correctly. 
    
    In other words, this is how the state is updated:
    
        { rem(rem_args) * client_state(rem_args, args) &*& atomic_space(stack(stack, ?elems) &*& all_clients_inv(stack, elems, args)) }
        operation()
        { rem(rem_args) * nclient_state(rem_args, args) &*& atomic_space(stack(stack, ?nelems) &*& all_clients_inv(stack, nelems, args)) }
    
    When composing multiple operations, it is impossible to hardcode the invariant of the atomic space as the separated
    conjunction of the stack with its client invariants.  Therefore, the invariant of the atomic space is left open and 
    each operation requires lemma's to open and close it.
    
*/

/*@

predicate_family stack_push_operation_pre(void *op)(struct stack *stack, void *data);
predicate_family stack_push_operation_post(void *op)();

typedef lemma void stack_push_operation();
    requires stack_push_operation_pre(this)(?stack, ?data) &*& stack(stack, ?elems);
    ensures stack_push_operation_post(this)() &*& stack(stack, cons(data, elems));

predicate_family stack_push_context_pre(void *ctxt)(stack_unsep* unsep, struct stack *stack, void *data, any args);
predicate_family stack_push_context_post(void *ctxt)(any args);

typedef lemma void stack_push_context(stack_push_operation *op);
    requires
        stack_push_context_pre(this)(?unsep, ?stack, ?data, ?args) &*& 
        stack(stack, ?elems) &*& 
        stack_unsep(unsep)(args, stack, ?inv, ?sep, elems) &*& 
        is_stack_push_operation(op) &*&
        stack_push_operation_pre(op)(stack, data);
    ensures
        stack_push_operation_post(op)() &*& 
        stack(stack, cons(data, elems)) &*& 
        stack_unsep(unsep)(args, stack, inv, sep, cons(data, elems)) &*& 
        is_stack_push_operation(op) &*&
        stack_push_context_post(this)(args);


@*/

void stack_push(struct stack *stack, void *data);
    /*@
    requires 
        stack_inv_info(?args, stack, ?inv, ?sep, ?unsep) &*&
        is_stack_push_context(?context) &*&
        stack_push_context_pre(context)(unsep, stack, data, args) &*&
        [?f] atomic_space(inv);
    @*/
    /*@
    ensures 
        stack_inv_info(args, stack, inv, sep, unsep) &*&
        is_stack_push_context(context) &*&
        [f] atomic_space(inv) &*& 
        stack_push_context_post(context)(args);
    @*/

/*@

predicate_family stack_try_pop_operation_pre(void *op)(struct stack *stack);
predicate_family stack_try_pop_operation_post(void *op)(bool succes, void* result);

fixpoint t head_or<t>(list<t> l, t def) {
    switch(l) {
        case nil: return def;
        case cons(h, l0): return h;
    }
}

typedef lemma void stack_try_pop_operation();
    requires stack_try_pop_operation_pre(this)(?stack) &*& stack(stack, ?elems);
    ensures stack_try_pop_operation_post(this)(elems != nil, head_or(elems, 0)) &*& 
        stack(stack, tail(elems));

predicate_family stack_try_pop_context_pre(void *ctxt)(stack_unsep* unsep, struct stack *stack, any args);
predicate_family stack_try_pop_context_post(void *ctxt)(bool succes, void* result, any args);

typedef lemma void stack_try_pop_context(stack_try_pop_operation *op);
    requires
        stack_try_pop_context_pre(this)(?unsep, ?stack, ?args) &*& 
        stack(stack, ?elems) &*& 
        stack_unsep(unsep)(args, stack, ?inv, ?sep, elems) &*& 
        is_stack_try_pop_operation(op) &*&
        stack_try_pop_operation_pre(op)(stack);
    ensures
        stack_try_pop_operation_post(op)(?success, ?result) &*& 
        stack(stack, tail(elems)) &*& 
        stack_unsep(unsep)(args, stack, inv, sep, tail(elems)) &*& 
        is_stack_try_pop_operation(op) &*&
        stack_try_pop_context_post(this)(success, result, args);

@*/

bool stack_try_pop(struct stack *stack, void** resultRef);
    /*@
    requires
        stack_inv_info(?args, stack, ?inv, ?sep, ?unsep) &*&
        is_stack_try_pop_context(?context) &*&
        stack_try_pop_context_pre(context)(unsep, stack, args) &*&
        [?f] atomic_space(inv) &*&
        pointer(resultRef, _);
    @*/
    /*@
    ensures 
        stack_inv_info(args, stack, inv, sep, unsep) &*&
        is_stack_try_pop_context(context) &*&
        stack_try_pop_context_post(context)(result, ?data, args) &*&        
        [f] atomic_space(inv) &*&
        pointer(resultRef, data);
    @*/


#endif
