#include "stack_leaking.h"
#include "stdlib.h"

struct value {
    int val;
};

/*@

//general predicate about value struct

predicate value(struct value* v; int val) = malloc_block_value(v) &*& v != 0 &*& v->val |-> val;

@*/


/*@

//lemma's to update stack_allClients in the atomic space

predicate stack_allClients(struct stack* s, list<void*> elems, any args) = true;

predicate_ctor stack_inv(struct stack *stack, any args)() =
    stack(stack, ?elems) &*& stack_allClients(stack, elems, args);


predicate_family_instance stack_sep(stack_inv_sep)(any info, struct stack *stack, predicate() inv, stack_unsep *unsep) = 
    info == unit &*&
    inv == stack_inv(stack, info) &*&
    unsep == stack_inv_unsep;
predicate_family_instance stack_unsep(stack_inv_unsep)(any info, struct stack *stack, predicate() inv, stack_sep *sep, list<void*> elems) = 
    info == unit &*&
    inv == stack_inv(stack, info) &*&
    sep == stack_inv_sep &*&
    stack_allClients(stack, elems, info);
lemma void stack_inv_sep() : stack_sep 
    requires stack_sep(stack_inv_sep)(?info, ?stack, ?inv, ?unsep) &*& inv();
    ensures stack_unsep(unsep)(info, stack, inv, stack_inv_sep, ?elems) &*& stack(stack, elems);
{   
    open stack_sep(stack_inv_sep)(info, stack, inv, unsep);
    open stack_inv(stack, info)();
    close stack_unsep(stack_inv_unsep)(info, stack, inv, stack_inv_sep, _);
}
lemma void stack_inv_unsep() : stack_unsep
    requires stack_unsep(stack_inv_unsep)(?info, ?stack, ?inv, ?sep, ?elems) &*& stack(stack, elems);
    ensures stack_sep(sep)(info, stack, inv, stack_inv_unsep) &*& inv();
{
    open stack_unsep(stack_inv_unsep)(info, stack, inv, sep, elems);
    close stack_inv(stack, info)();
    close stack_sep(stack_inv_sep)(info, stack, inv, stack_inv_unsep);
}







predicate_family_instance stack_push_context_pre(allClients_push)(stack_unsep *unsep, struct stack *stack, void *data, any args) =
    unsep == stack_inv_unsep;
predicate_family_instance stack_push_context_post(allClients_push)(any args) =
    true;
lemma void allClients_push(stack_push_operation *op): stack_push_context
    requires
        stack_push_context_pre(allClients_push)(?unsep, ?stack, ?data, ?args) &*& 
        stack(stack, ?elems) &*& 
        stack_unsep(unsep)(args, stack, ?inv, ?sep, elems) &*& 
        is_stack_push_operation(op) &*&
        stack_push_operation_pre(op)(stack, data);
    ensures
        stack_push_operation_post(op)() &*& 
        stack(stack, cons(data, elems)) &*& 
        stack_unsep(unsep)(args, stack, inv, sep, cons(data, elems)) &*& 
        is_stack_push_operation(op) &*&
        stack_push_context_post(allClients_push)(args);
{
    open stack_push_context_pre(allClients_push)(unsep, stack, data, args);
    open stack_unsep(stack_inv_unsep)(args, stack, inv, sep, elems);
    open stack_allClients(stack, _, _);
    op();
    close stack_allClients(stack, cons(data, elems), args);
    close stack_unsep(stack_inv_unsep)(args, stack, inv, sep, cons(data, elems));
    close stack_push_context_post(allClients_push)(args);
}

predicate_family_instance stack_try_pop_context_pre(allClients_try_pop)(stack_unsep *unsep, struct stack *stack, any args) =
    unsep == stack_inv_unsep;
predicate_family_instance stack_try_pop_context_post(allClients_try_pop)(bool success, void* data, any args) =
    true;
lemma void allClients_try_pop(stack_try_pop_operation *op): stack_try_pop_context
    requires
        stack_try_pop_context_pre(allClients_try_pop)(?unsep, ?stack, ?args) &*& 
        stack(stack, ?elems) &*& 
        stack_unsep(unsep)(args, stack, ?inv, ?sep, elems) &*& 
        is_stack_try_pop_operation(op) &*&
        stack_try_pop_operation_pre(op)(stack);
    ensures
        stack_try_pop_operation_post(op)(?success, ?result) &*& 
        stack(stack, tail(elems)) &*& 
        stack_unsep(unsep)(args, stack, inv, sep, tail(elems)) &*& 
        is_stack_try_pop_operation(op) &*&
        stack_try_pop_context_post(allClients_try_pop)(success, result, args);
{
    open stack_try_pop_context_pre(allClients_try_pop)(unsep, stack, args);
    open stack_unsep(stack_inv_unsep)(args, stack, inv, sep, elems);
    open stack_allClients(stack, _, args);
    op();
    assert stack_try_pop_operation_post(op)(?suc, ?d);
    close stack_allClients(stack, tail(elems), args);
    close stack_unsep(stack_inv_unsep)(args, stack, inv, sep, tail(elems));
    close stack_try_pop_context_post(allClients_try_pop)(suc, d, args);
}
@*/

void test() 
//@ requires true;
//@ ensures true;
{
    struct value* v2, v3;
    struct stack* s = create_stack();
    //@ close stack_allClients(s, nil, unit);
    //@ produce_lemma_function_pointer_chunk(stack_inv_sep);
    //@ produce_lemma_function_pointer_chunk(stack_inv_unsep);
    //@ close stack_unsep(stack_inv_unsep)(unit, s, stack_inv(s, unit), stack_inv_sep, nil);
    //@ share_stack(s);
    
    
    struct value* v = malloc(sizeof(struct value));
    if(v == 0) abort();
    v->val = 27;    
    //@ close stack_push_context_pre(allClients_push)(stack_inv_unsep, s, v, unit);
    //@ produce_lemma_function_pointer_chunk(allClients_push);
    stack_push(s, v);
    //@ leak is_stack_push_context(allClients_push);
    //@ open stack_push_context_post(allClients_push)(unit);
    
    //@ close stack_try_pop_context_pre(allClients_try_pop)(stack_inv_unsep, s, unit);
    //@ produce_lemma_function_pointer_chunk(allClients_try_pop);
    bool result = stack_try_pop(s, &v2);
    //@ leak is_stack_try_pop_context(allClients_try_pop);
    //@ open stack_try_pop_context_post(allClients_try_pop)(_, _, unit);

    //@ unshare_stack(s);
    //@ open stack_unsep(stack_inv_unsep)(unit, s, stack_inv(s, unit), stack_inv_sep, _);
    //@ leak is_stack_sep(stack_inv_sep);
    //@ leak is_stack_unsep(stack_inv_unsep);
    
    bool hasMore = true;
    while(hasMore)
    //@ invariant stack(s, ?remElems) &*& stack_allClients(s, remElems, unit) &*& pointer(&v3, _) &*& (hasMore ? true: remElems == nil);
    {
        hasMore = stack_try_pop_sequential(s, &v3);
        //@ open stack_allClients(s, remElems, unit); 
        //@ close stack_allClients(s, tail(remElems), unit); 
    }
    
    //@ open stack_allClients(s, _, unit);
    dispose_stack(s);

    free(v);
}

/*@

//lemma's to update stack_allClients2 in the atomic space

predicate value_helper(struct value* v) = value(v, _);

predicate stack_allClients2(struct stack* s, list<void*> elems, any args) = foreach(elems, value_helper);

predicate_ctor stack_inv2(struct stack *stack, any args)() =
    stack(stack, ?elems) &*& stack_allClients2(stack, elems, args);

predicate_family_instance stack_sep(stack_inv2_sep)(any info, struct stack *stack, predicate() inv, stack_unsep *unsep) = 
    info == unit &*&
    inv == stack_inv2(stack, info) &*&
    unsep == stack_inv2_unsep;
predicate_family_instance stack_unsep(stack_inv2_unsep)(any info, struct stack *stack, predicate() inv, stack_sep *sep, list<void*> elems) = 
    info == unit &*&
    inv == stack_inv2(stack, info) &*&
    sep == stack_inv2_sep &*&
    stack_allClients2(stack, elems, info);
lemma void stack_inv2_sep() : stack_sep 
    requires stack_sep(stack_inv2_sep)(?info, ?stack, ?inv, ?unsep) &*& inv();
    ensures stack_unsep(unsep)(info, stack, inv, stack_inv2_sep, ?elems) &*& stack(stack, elems);
{   
    open stack_sep(stack_inv2_sep)(info, stack, inv, unsep);
    open stack_inv2(stack, info)();
    close stack_unsep(stack_inv2_unsep)(info, stack, inv, stack_inv2_sep, _);
}
lemma void stack_inv2_unsep() : stack_unsep
    requires stack_unsep(stack_inv2_unsep)(?info, ?stack, ?inv, ?sep, ?elems) &*& stack(stack, elems);
    ensures stack_sep(sep)(info, stack, inv, stack_inv2_unsep) &*& inv();
{
    open stack_unsep(stack_inv2_unsep)(info, stack, inv, sep, elems);
    close stack_inv2(stack, info)();
    close stack_sep(stack_inv2_sep)(info, stack, inv, stack_inv2_unsep);
}

predicate_family_instance stack_push_context_pre(allClients2_push)(stack_unsep *unsep, struct stack *stack, void *data, any args) =
    unsep == stack_inv2_unsep &*& value(data, _);
predicate_family_instance stack_push_context_post(allClients2_push)(any args) =
    true;
lemma void allClients2_push(stack_push_operation *op): stack_push_context
    requires
        stack_push_context_pre(allClients2_push)(?unsep, ?stack, ?data, ?args) &*& 
        stack(stack, ?elems) &*& 
        stack_unsep(unsep)(args, stack, ?inv, ?sep, elems) &*& 
        is_stack_push_operation(op) &*&
        stack_push_operation_pre(op)(stack, data);
    ensures
        stack_push_operation_post(op)() &*& 
        stack(stack, cons(data, elems)) &*& 
        stack_unsep(unsep)(args, stack, inv, sep, cons(data, elems)) &*& 
        is_stack_push_operation(op) &*&
        stack_push_context_post(allClients2_push)(args);
{
    open stack_push_context_pre(allClients2_push)(unsep, stack, data, args);
    open stack_unsep(stack_inv2_unsep)(args, stack, inv, sep, elems);
    open stack_allClients2(stack, elems, args);
    op();
    close value_helper(data);
    close foreach(cons(data, elems), value_helper);
    close stack_allClients2(stack, cons(data, elems), args);
    close stack_unsep(stack_inv2_unsep)(args, stack, inv, sep, cons(data, elems));
    close stack_push_context_post(allClients2_push)(args);
}

predicate_family_instance stack_try_pop_context_pre(allClients2_try_pop)(stack_unsep* unsep, struct stack *stack, any args) =
    unsep == stack_inv2_unsep;
predicate_family_instance stack_try_pop_context_post(allClients2_try_pop)(bool success, void* data, any args) =
    success ? value(data, _) : true ;
lemma void allClients2_try_pop(stack_try_pop_operation *op): stack_try_pop_context
    requires
        stack_try_pop_context_pre(allClients2_try_pop)(?unsep, ?stack, ?args) &*& 
        stack(stack, ?elems) &*& 
        stack_unsep(unsep)(args, stack, ?inv, ?sep, elems) &*& 
        is_stack_try_pop_operation(op) &*&
        stack_try_pop_operation_pre(op)(stack);
    ensures
        stack_try_pop_operation_post(op)(?success, ?result) &*& 
        stack(stack, tail(elems)) &*& 
        stack_unsep(unsep)(args, stack, inv, sep, tail(elems)) &*& 
        is_stack_try_pop_operation(op) &*&
        stack_try_pop_context_post(allClients2_try_pop)(success, result, args);
{
    open stack_try_pop_context_pre(allClients2_try_pop)(unsep, stack, args);
    open stack_unsep(stack_inv2_unsep)(args, stack, inv, sep, elems);
    open stack_allClients2(stack, elems, args);
    op();
    assert stack_try_pop_operation_post(op)(?suc, ?d);
    if(suc) {
        open foreach(elems, value_helper);
        open value_helper(d);
    }
    close stack_allClients2(stack, tail(elems), args);
    close stack_unsep(stack_inv2_unsep)(args, stack, inv, sep, tail(elems));
    close stack_try_pop_context_post(allClients2_try_pop)(suc, d, args);
}

@*/

void test2() 
//@ requires true;
//@ ensures true;
{
    struct value* v2, v3;
    struct stack* s = create_stack();
    //@ close foreach(nil, value_helper);
    //@ close stack_allClients2(s, nil, unit);
    //@ close stack_unsep(stack_inv2_unsep)(unit, s, stack_inv2(s, unit), stack_inv2_sep, nil);
    //@ produce_lemma_function_pointer_chunk(stack_inv2_sep);
    //@ produce_lemma_function_pointer_chunk(stack_inv2_unsep);
    //@ share_stack(s);

    struct value* v = malloc(sizeof(struct value));
    if(v == 0) abort();
    v->val = 27;
    
    //@ close stack_push_context_pre(allClients2_push)(stack_inv2_unsep, s, v, unit);
    //@ produce_lemma_function_pointer_chunk(allClients2_push);
    stack_push(s, v);
    //@ leak is_stack_push_context(allClients2_push);
    //@ open stack_push_context_post(allClients2_push)(unit);
    
    //@ close stack_try_pop_context_pre(allClients2_try_pop)(stack_inv2_unsep, s, unit);
    //@ produce_lemma_function_pointer_chunk(allClients2_try_pop);
    bool result = stack_try_pop(s, &v2);
    //@ leak is_stack_try_pop_context(allClients2_try_pop);
    //@ open stack_try_pop_context_post(allClients2_try_pop)(_, _, unit);
    if(result) { 
        //@ open value(v2, _);
        free(v2); 
    }

    //@ unshare_stack(s);
    //@ open stack_unsep(stack_inv2_unsep)(unit, s, stack_inv2(s, unit), stack_inv2_sep, _);
    //@ leak is_stack_sep(stack_inv2_sep);
    //@ leak is_stack_unsep(stack_inv2_unsep);
    
    bool hasMore = true;
    while(hasMore)
    //@ invariant stack(s, ?remElems) &*& stack_allClients2(s, remElems, unit) &*& pointer(&v3, _) &*& (hasMore ? true: remElems == nil);
    {
        hasMore = stack_try_pop_sequential(s, &v3);
        if(hasMore) {
            //@ open stack_allClients2(s, remElems, unit);
            //@ open foreach(remElems, value_helper);
            //@ close stack_allClients2(s, tail(remElems), unit);
            //@ open value_helper(v3);
            //@ open value(v3, _);
            free(v3); 
        }
        
    }
    
    //@ open stack_allClients2(s, remElems, unit);
    //@ open foreach(remElems, value_helper);
    dispose_stack(s);
}


/*@

//lemma's to update stack_allClients in the atomic space

predicate_ctor value_helper2(int val)(struct value* v) = value(v, val);

predicate stack_allClients3(struct stack* s, list<void*> elems, int v) = foreach(elems, value_helper2(v));

predicate_ctor stack_inv3(struct stack *stack, int v)() =
    stack(stack, ?elems) &*& stack_allClients3(stack, elems, v);

predicate_family_instance stack_sep(stack_inv3_sep)(boxed_int info, struct stack *stack, predicate() inv, stack_unsep *unsep) = 
    switch(info) {
        case boxed_int(v): return
            inv == stack_inv3(stack, v) &*&
            unsep == stack_inv3_unsep;
    };
predicate_family_instance stack_unsep(stack_inv3_unsep)(boxed_int info, struct stack *stack, predicate() inv, stack_sep *sep, list<void*> elems) = 
    switch(info) {
        case boxed_int(v): return
            inv == stack_inv3(stack, v) &*&
            sep == stack_inv3_sep &*&
            stack_allClients3(stack, elems, v);
    };
lemma void stack_inv3_sep() : stack_sep 
    requires stack_sep(stack_inv3_sep)(?info, ?stack, ?inv, ?unsep) &*& inv();
    ensures stack_unsep(unsep)(info, stack, inv, stack_inv3_sep, ?elems) &*& stack(stack, elems);
{   
    open stack_sep(stack_inv3_sep)(?info2, stack, inv, unsep);
    switch(info2) {
        case boxed_int(v):
            open stack_inv3(stack, v)();
            close stack_unsep(stack_inv3_unsep)(info2, stack, inv, stack_inv3_sep, _);
    }
}
lemma void stack_inv3_unsep() : stack_unsep
    requires stack_unsep(stack_inv3_unsep)(?info, ?stack, ?inv, ?sep, ?elems) &*& stack(stack, elems);
    ensures stack_sep(sep)(info, stack, inv, stack_inv3_unsep) &*& inv();
{
    open stack_unsep(stack_inv3_unsep)(?info2, stack, inv, sep, elems);
    switch(info2) {
        case boxed_int(v):
            close stack_inv3(stack, v)();
            close stack_sep(stack_inv3_sep)(info2, stack, inv, stack_inv3_unsep);
    }
}



predicate_family_instance stack_push_context_pre(allClients3_push)(stack_unsep* unsep, struct stack *stack, void *data, boxed_int args) =
    switch(args) {
        case boxed_int(v): return
            unsep == stack_inv3_unsep &*& value(data, unboxed_int(args));
    };
predicate_family_instance stack_push_context_post(allClients3_push)(boxed_int args) =
    true;
lemma void allClients3_push(stack_push_operation *op): stack_push_context
    requires
        stack_push_context_pre(allClients3_push)(?unsep, ?stack, ?data, ?args) &*& 
        stack(stack, ?elems) &*& 
        stack_unsep(unsep)(args, stack, ?inv, ?sep, elems) &*& 
        is_stack_push_operation(op) &*&
        stack_push_operation_pre(op)(stack, data);
    ensures
        stack_push_operation_post(op)() &*& 
        stack(stack, cons(data, elems)) &*& 
        stack_unsep(unsep)(args, stack, inv, sep, cons(data, elems)) &*& 
        is_stack_push_operation(op) &*&
        stack_push_context_post(allClients3_push)(args);
{
    open stack_push_context_pre(allClients3_push)(unsep, stack, data, ?args2);
    open stack_unsep(stack_inv3_unsep)(args2, stack, inv, sep, elems);
    open stack_allClients3(stack, elems, ?v);
    op();
    close value_helper2(v)(data);
    close foreach(cons(data, elems), value_helper2(v));
    close stack_allClients3(stack, cons(data, elems), v);
    close stack_unsep(stack_inv3_unsep)(args2, stack, inv, sep, cons(data, elems));
    close stack_push_context_post(allClients3_push)(args2);
}

predicate_family_instance stack_try_pop_context_pre(allClients3_try_pop)(stack_unsep* unsep, struct stack *stack, boxed_int args) =
    unsep == stack_inv3_unsep;
predicate_family_instance stack_try_pop_context_post(allClients3_try_pop)(bool success, void* data, boxed_int args) =
    switch(args) {
        case boxed_int(v): return
            success ? value(data, v) : true ;
    };    
lemma void allClients3_try_pop(stack_try_pop_operation *op): stack_try_pop_context
    requires
        stack_try_pop_context_pre(allClients3_try_pop)(?unsep, ?stack, ?args) &*& 
        stack(stack, ?elems) &*& 
        stack_unsep(unsep)(args, stack, ?inv, ?sep, elems) &*& 
        is_stack_try_pop_operation(op) &*&
        stack_try_pop_operation_pre(op)(stack);
    ensures
        stack_try_pop_operation_post(op)(?success, ?result) &*& 
        stack(stack, tail(elems)) &*& 
        stack_unsep(unsep)(args, stack, inv, sep, tail(elems)) &*& 
        is_stack_try_pop_operation(op) &*&
        stack_try_pop_context_post(allClients3_try_pop)(success, result, args);
{
    open stack_try_pop_context_pre(allClients3_try_pop)(unsep, stack, ?args2);
    open stack_unsep(stack_inv3_unsep)(args2, stack, inv, sep, elems);
    open stack_allClients3(stack, elems, ?v);
    op();
    assert stack_try_pop_operation_post(op)(?suc, ?d);
    if(suc) {
        open foreach(elems, value_helper2(v));
        open value_helper2(v)(d);
    }
    close stack_allClients3(stack, tail(elems), v);
    close stack_unsep(stack_inv3_unsep)(args2, stack, inv, sep, tail(elems));
    close stack_try_pop_context_post(allClients3_try_pop)(suc, d, args2);
}

@*/

void test3() 
//@ requires true;
//@ ensures true;
{
    struct value* v2, v3;
    struct stack* s = create_stack();
    //@ close foreach(nil, value_helper2(27));
    //@ close stack_allClients3(s, nil, 27);
    //@ close stack_unsep(stack_inv3_unsep)(boxed_int(27), s, stack_inv3(s, 27), stack_inv3_sep, nil);
    //@ produce_lemma_function_pointer_chunk(stack_inv3_sep);
    //@ produce_lemma_function_pointer_chunk(stack_inv3_unsep);    
    //@ share_stack(s);
        
    struct value* v = malloc(sizeof(struct value));
    if(v == 0) abort();
    v->val = 27;
    
    //@ close stack_push_context_pre(allClients3_push)(stack_inv3_unsep, s, v, boxed_int(27));
    //@ produce_lemma_function_pointer_chunk(allClients3_push);
    stack_push(s, v);
    //@ leak is_stack_push_context(allClients3_push);
    //@ open stack_push_context_post(allClients3_push)(boxed_int(27));
    
    //@ close stack_try_pop_context_pre(allClients3_try_pop)(stack_inv3_unsep, s, boxed_int(27));
    //@ produce_lemma_function_pointer_chunk(allClients3_try_pop);
    bool result = stack_try_pop(s, &v2);
    //@ leak is_stack_try_pop_context(allClients3_try_pop);
    //@ open stack_try_pop_context_post(allClients3_try_pop)(_, _, boxed_int(27));
    if(result) { 
        //@ open value(v2, 27);
        free(v2); 
    }

    //@ unshare_stack(s);
    //@ open stack_unsep(stack_inv3_unsep)(boxed_int(27), s, stack_inv3(s, 27), stack_inv3_sep, _);
    //@ leak is_stack_sep(stack_inv3_sep);
    //@ leak is_stack_unsep(stack_inv3_unsep);
    
    
    bool hasMore = true;
    while(hasMore)
    //@ invariant stack(s, ?remElems) &*& stack_allClients3(s, remElems, 27) &*& pointer(&v3, _) &*& (hasMore ? true: remElems == nil);
    {
        hasMore = stack_try_pop_sequential(s, &v3);
        if(hasMore) {
            //@ open stack_allClients3(s, remElems, 27);
            //@ open foreach(remElems, value_helper2(27));
            //@ close stack_allClients3(s, tail(remElems), 27);
            //@ open value_helper2(27)(v3);
            //@ open value(v3, 27);
            free((struct value*)v3); 
        }
    }
    
    //@ open stack_allClients3(s, remElems, 27);
    //@ open foreach(remElems, value_helper2(27));
    dispose_stack(s);
}
