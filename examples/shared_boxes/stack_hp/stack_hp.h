#ifndef STACK_HP_H
#define STACK_HP_H

#include "atomics.h"

struct stack;
struct stack_client;

/*@

predicate stack(struct stack *stack; int allClientsId, list<void*> elems);
predicate stack_local(struct stack *stack; int allClientsId);

predicate stack_client_local(struct stack_client* client, struct stack *stack, int allClientsId);


predicate_family stack_sep(void *sep)(any info, struct stack *stack, int allClientsId, predicate() inv, stack_unsep *unsep);
predicate_family stack_unsep(void *unsep)(any info, struct stack *stack, int allClientsId, predicate() inv, stack_sep *sep, list<void*> elems);

typedef lemma void stack_sep();
    requires stack_sep(this)(?info, ?stack, ?allClientsId, ?inv, ?unsep) &*& inv();
    ensures stack_unsep(unsep)(info, stack, allClientsId, inv, this, ?elems) &*& stack(stack, allClientsId, elems);

typedef lemma void stack_unsep();
    requires stack_unsep(this)(?info, ?stack, ?allClientsId, ?inv, ?sep, ?elems) &*& stack(stack, allClientsId, elems);
    ensures stack_sep(sep)(info, stack, allClientsId, inv, this) &*& inv();

predicate stack_inv_info(any info, struct stack *stack, int allClientsId, predicate() inv, stack_sep* sep, stack_unsep* unsep);

@*/

// creating and disposing stacks

struct stack *create_stack();
    //@ requires true;
    //@ ensures stack(result, _, nil);

void dispose_stack(struct stack *stack);
    //@ requires stack(stack, _, nil);
    //@ ensures true;

// sequential operations on stacks

void stack_push_sequential(struct stack *stack, void *data);
    //@ requires stack(stack, ?allClientsId, ?elems);
    //@ ensures stack(stack, allClientsId, cons(data, elems));

bool stack_try_pop_sequential(struct stack *stack, void** resultRef);
    //@ requires stack(stack, ?allClientsId, ?elems) &*& pointer(resultRef, _);
    //@ ensures stack(stack, allClientsId, tail(elems)) &*& pointer(resultRef, head_or(elems, 0)) &*& result == (elems != nil);

// lemma's to share and unshare stacks 
/*@

lemma void share_stack(struct stack *stack);
    requires 
        stack(stack, ?allClientsId, ?elems) &*&
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
// concurrent operations to create and dispose stack clients

struct stack_client* stack_create_client(struct stack *stack);
    /*@
    requires
        stack_inv_info(?args, stack, ?inv, ?sep, ?unsep) &*&
        [?f] atomic_space(inv);
    @*/
    /*@
    ensures
        stack_inv_info(args, stack, inv, sep, unsep) &*&
        [f] atomic_space(inv) &*& 
        stack_client(stack, result);
    @*/

void stack_dispose_client(struct stack *stack, struct stack_client* client);
    /*@
    requires
        stack_inv_info(?args, stack, ?inv, ?sep, ?unsep) &*&
        [?f] atomic_space(inv) &*& 
        stack_client(stack, client);
    @*/
    /*@
    ensures
        stack_inv_info(args, stack, inv, sep, unsep) &*&
        [f] atomic_space(inv);
    @*/

// concurrent operations on stacks

/*@

predicate_family stack_push_operation_pre(void *op)(struct stack *stack, void *data);
predicate_family stack_push_operation_post(void *op)();

typedef lemma void stack_push_operation();
    requires stack_push_operation_pre(this)(?stack, ?data) &*& stack(stack, ?allClientsId, ?elems);
    ensures stack_push_operation_post(this)() &*& stack(stack, allClientsId, cons(data, elems));

predicate_family stack_push_context_pre(void *ctxt)(stack_unsep* unsep, struct stack *stack, int allClientsId, void *data, any args);
predicate_family stack_push_context_post(void *ctxt)(any args);

typedef lemma void stack_push_context(stack_push_operation *op);
    requires
        stack_push_context_pre(this)(?unsep, ?stack, ?allClientsId, ?data, ?args) &*& 
        stack(stack, allClientsId, ?elems) &*& 
        stack_unsep(unsep)(args, stack, allClientsId, ?inv, ?sep, elems) &*& 
        is_stack_push_operation(op) &*&
        stack_push_operation_pre(op)(stack, data);
    ensures
        stack_push_operation_post(op)() &*& 
        stack(stack, allClientsId, cons(data, elems)) &*& 
        stack_unsep(unsep)(args, stack, allClientsId, inv, sep, cons(data, elems)) &*& 
        is_stack_push_operation(op) &*&
        stack_push_context_post(this)(args);


@*/

void stack_push(struct stack *stack, struct stack_client *client, void *data);
    /*@
    requires 
        stack_inv_info(?args, stack, ?inv, ?sep, ?unsep) &*&
        is_stack_push_context(?context) &*&
        stack_push_context_pre(context)(unsep, stack, data, args) &*&
        [?f] atomic_space(inv) &*& 
        stack_client(stack, client);
    @*/
    /*@
    ensures 
        stack_inv_info(args, stack, inv, sep, unsep) &*&
        is_stack_push_context(context) &*&
        [f] atomic_space(inv) &*& 
        stack_push_context_post(context)(args) &*& 
        stack_client(stack, client);
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
    requires stack_try_pop_operation_pre(this)(?stack) &*& stack(stack, ?allClientsId, ?elems);
    ensures stack_try_pop_operation_post(this)(elems != nil, head_or(elems, 0)) &*& 
        stack(stack, allClientsId, tail(elems));

predicate_family stack_try_pop_context_pre(void *ctxt)(stack_unsep* unsep, struct stack *stack, int allClientsId, any args);
predicate_family stack_try_pop_context_post(void *ctxt)(bool succes, void* result, any args);

typedef lemma void stack_try_pop_context(stack_try_pop_operation *op);
    requires
        stack_try_pop_context_pre(this)(?unsep, ?stack, ?allClientsId, ?args) &*& 
        stack(stack, allClientsId, ?elems) &*& 
        stack_unsep(unsep)(args, stack, allClientsId, ?inv, ?sep, elems) &*& 
        is_stack_try_pop_operation(op) &*&
        stack_try_pop_operation_pre(op)(stack);
    ensures
        stack_try_pop_operation_post(op)(?success, ?result) &*& 
        stack(stack, allClientsId, tail(elems)) &*& 
        stack_unsep(unsep)(args, stack, allClientsId, inv, sep, tail(elems)) &*& 
        is_stack_try_pop_operation(op) &*&
        stack_try_pop_context_post(this)(success, result, args);

@*/

bool stack_try_pop(struct stack *stack, struct stack_client *client, void** resultRef);
    /*@
    requires
        stack_inv_info(?args, stack, ?inv, ?sep, ?unsep) &*&
        is_stack_try_pop_context(?context) &*&
        stack_try_pop_context_pre(context)(unsep, stack, args) &*&
        [?f] atomic_space(inv) &*& 
        stack_client(stack, client)&*&
        pointer(resultRef, _);
    @*/
    /*@
    ensures 
        stack_inv_info(args, stack, inv, sep, unsep) &*&
        is_stack_try_pop_context(context) &*&
        stack_try_pop_context_post(context)(result, ?data, args) &*&        
        [f] atomic_space(inv) &*& 
        stack_client(stack, client) &*&
        pointer(resultRef, data);
    @*/


#endif
