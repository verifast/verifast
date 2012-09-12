#include "stack_leaking.h"
#include "stdlib.h"

struct node {
    void *data;
    struct node *next;
};

struct stack {
    struct node *head;
};

/*@

predicate node(struct node *node; struct node *next, void *data) = 
    malloc_block_node(node) &*&
    node != 0 &*&
    node->next |-> next &*&
    node->data |-> data;

predicate lseg(struct node *first, struct node *last; list<void *> nodes, list<void *> elems) =
    first == last ?
        nodes == nil &*&
        elems == nil
    :
        [_]node(first, ?next, ?data) &*& 
        lseg(next, last, ?nodes0, ?elems0) &*&
        nodes == cons(first, nodes0) &*&
        elems == cons(data, elems0);

predicate stack(struct stack *stack; list<void*> elems) =
    malloc_block_stack(stack) &*&
    stack->head |-> ?head &*& 
    lseg(head, 0, ?nodes, elems);

predicate stack_inv_info(any info, struct stack *stack, predicate() inv, stack_sep* sep, stack_unsep* unsep) =
    is_stack_sep(sep) &*&
    is_stack_unsep(unsep) &*&
    stack_sep(sep)(info, stack, inv, unsep);

@*/

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, nil);
{
    struct stack *s = malloc(sizeof(struct stack));
    if (s == 0) abort();
    s->head = 0;
    //@ close lseg(0, 0, nil, nil);
    //@ close stack(s, nil);
    return s;
}

void dispose_stack(struct stack *stack)
    //@ requires stack(stack, nil);
    //@ ensures true;
{
    //@ open stack(stack, nil);
    //@ struct node* head = stack->head;
    //@ open lseg(head, 0, _, nil);
    free(stack);
}



void stack_push(struct stack *stack, void *data)
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
{
    struct node *node = malloc(sizeof(struct node));
    if (node == 0) abort();
    node->data = data;
    node->next = 0;
    
    bool succeeded = false;
    while(!succeeded) 
    /*@
    invariant [f] atomic_space(inv) &*& is_stack_push_context(context) &*&
        stack_inv_info(args, stack, inv, sep, unsep) &*&
        succeeded ? stack_push_context_post(context)(args) : node(node, _, data) &*& stack_push_context_pre(context)(unsep, stack, data, args);
    @*/
    {
        struct node *h = 0;
        //@ struct node *hProphecy = create_prophecy_pointer();
        {
            /*@
            predicate_family_instance atomic_load_pointer_context_pre(icontext)(predicate() iinv, void **pp, void *prophecy) =
                iinv == inv &*&
                pp == &stack->head &*& 
                prophecy == hProphecy  &*&
                stack_inv_info(args, stack, inv, sep, unsep);
            predicate_family_instance atomic_load_pointer_context_post(icontext)() = 
                stack_inv_info(args, stack, inv, sep, unsep);
            lemma void icontext(atomic_load_pointer_operation *op) : atomic_load_pointer_context
                requires
                    atomic_load_pointer_context_pre(icontext)(?iinv, ?pp, ?prophecy) &*& iinv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
                ensures
                    atomic_load_pointer_context_post(icontext)() &*& iinv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
            {
                open atomic_load_pointer_context_pre(icontext)(iinv, pp, prophecy);
                open stack_inv_info(args, stack, inv, sep, unsep);
                sep();
                open stack(stack, ?elems);
                op();
                close stack(stack, elems);
                unsep();
                close stack_inv_info(args, stack, inv, sep, unsep);
                close atomic_load_pointer_context_post(icontext)();
            }
            @*/
            //@ close atomic_load_pointer_context_pre(icontext)(inv, &stack->head, hProphecy);
            //@ produce_lemma_function_pointer_chunk(icontext);
            h = atomic_load_pointer(&stack->head);
            //@ open atomic_load_pointer_context_post(icontext)();
            //@ leak is_atomic_load_pointer_context(icontext);
        }
        
        node->next = h;
        
        struct node *casResult;
        //@ struct node *casResultProphecy = create_prophecy_pointer();
        {
            /*@
            predicate_family_instance atomic_compare_and_store_pointer_context_pre(icontext)(predicate() iinv, void **pp, void *old, void *new, void *prophecy) = 
                iinv == inv &*& 
                pp == &stack->head &*& 
                old == h &*& 
                new == node &*& 
                prophecy == casResultProphecy &*& //end of argument fixing
                node(node, h, data) &*&
                is_stack_push_context(context) &*&
                stack_push_context_pre(context)(unsep, stack, data, args) &*&
                stack_inv_info(args, stack, inv, sep, unsep);
            predicate_family_instance atomic_compare_and_store_pointer_context_post(icontext)() = 
                is_stack_push_context(context) &*&
                stack_inv_info(args, stack, inv, sep, unsep) &*&
                casResultProphecy == h ? stack_push_context_post(context)(args) : node(node, h, data) &*& stack_push_context_pre(context)(unsep, stack, data, args); 
            lemma void icontext(atomic_compare_and_store_pointer_operation *op):atomic_compare_and_store_pointer_context
                requires
                    atomic_compare_and_store_pointer_context_pre(icontext)(?iinv, ?pp, ?old, ?new, ?prophecy) &*& iinv() &*&
                    is_atomic_compare_and_store_pointer_operation(op) &*&
                    atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
                ensures
                    atomic_compare_and_store_pointer_context_post(icontext)() &*& iinv() &*&
                    is_atomic_compare_and_store_pointer_operation(op) &*&
                    atomic_compare_and_store_pointer_operation_post(op)();
            {
                open atomic_compare_and_store_pointer_context_pre(icontext)(iinv, pp, old, new, prophecy);
                open stack_inv_info(args, stack, inv, sep, unsep);
                sep();
                if(prophecy == h) {
                    {
                        predicate_family_instance stack_push_operation_pre(operation)(struct stack *stack2, void *data2) =
                            stack2 == stack &*& 
                            data2 == data &*&
                            is_atomic_compare_and_store_pointer_operation(op) &*&
                            atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy) &*&
                            node(node, h, data);
                        predicate_family_instance stack_push_operation_post(operation)() = 
                            is_atomic_compare_and_store_pointer_operation(op) &*&
                            atomic_compare_and_store_pointer_operation_post(op)();
                        lemma void operation() : stack_push_operation
                            requires stack_push_operation_pre(operation)(?stack2, ?data2) &*& stack(stack2, ?elems);
                            ensures stack_push_operation_post(operation)() &*& stack(stack2, cons(data2, elems));
                        {
                            open stack_push_operation_pre(operation)(stack2, data2);
                            open stack(stack, elems);
                            op();
                            assert lseg(h, 0, ?nodes, elems);
                            leak node(node, h, data);
                            close lseg(node, 0, cons(node, nodes), cons(data, elems));
                            close stack(stack, _);
                            close stack_push_operation_post(operation)();
                        }
                        close stack_push_operation_pre(operation)(stack, data);
                        produce_lemma_function_pointer_chunk(operation) {
                            context(operation);
                        }
                        open stack_push_operation_post(operation)();
                    }
                } else {
                    open stack(stack, ?elems);
                    op();
                    close stack(stack, _);
                }
                unsep();
                close stack_inv_info(args, stack, inv, sep, unsep);
                close atomic_compare_and_store_pointer_context_post(icontext)();
            }
            @*/
            //@ close atomic_compare_and_store_pointer_context_pre(icontext)(inv, &stack->head, h, node, casResultProphecy);
            //@ produce_lemma_function_pointer_chunk(icontext);
            casResult = atomic_compare_and_store_pointer(&stack->head, h, node);
            //@ open atomic_compare_and_store_pointer_context_post(icontext)();
            //@ leak is_atomic_compare_and_store_pointer_context(icontext);
        }
        succeeded = (casResult == h);
    }
}

bool stack_try_pop(struct stack *stack, void** resultRef)
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
{
    bool succeeded = false;
    bool success = false;
    void* result = 0;
    while (!succeeded) 
    /*@ invariant is_stack_try_pop_context(context) &*& [f] atomic_space(inv) &*& 
            stack_inv_info(args, stack, inv, sep, unsep) &*&
            ( succeeded ? stack_try_pop_context_post(context)(success, result, args) : stack_try_pop_context_pre(context)(unsep, stack, args));
    @*/
    {
        struct node *h;
        //@ struct node *hProphecy = create_prophecy_pointer();
        {
            /*@
            predicate_family_instance atomic_load_pointer_context_pre(icontext)(predicate() iinv, void **pp, void *prophecy) =
                iinv == inv &*&
                pp == &stack->head &*& 
                prophecy == hProphecy &*&
                is_stack_try_pop_context(context) &*&
                stack_inv_info(args, stack, inv, sep, unsep) &*&
                stack_try_pop_context_pre(context)(unsep, stack, args); 
            predicate_family_instance atomic_load_pointer_context_post(icontext)() = 
                is_stack_try_pop_context(context) &*&
                stack_inv_info(args, stack, inv, sep, unsep) &*&
                ( hProphecy == 0 ? 
                    stack_try_pop_context_post(context)(false, 0, args) : 
                    [_]node(hProphecy, _, _) &*& stack_try_pop_context_pre(context)(unsep, stack, args) 
                );
            lemma void icontext(atomic_load_pointer_operation *op) : atomic_load_pointer_context
                requires
                    atomic_load_pointer_context_pre(icontext)(?iinv, ?pp, ?prophecy) &*& iinv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
                ensures
                    atomic_load_pointer_context_post(icontext)() &*& iinv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
            {
                open atomic_load_pointer_context_pre(icontext)(iinv, pp, prophecy);
                open stack_inv_info(args, stack, inv, sep, unsep);
                sep();
                if(hProphecy != 0) {
                    open stack(stack, ?elems);
                    op();
                    open lseg(hProphecy, 0, ?nodes, elems);
                    close lseg(hProphecy, 0, nodes, elems);
                    assert [_]node(hProphecy, _, _) &*& lseg(hProphecy, 0, nodes, elems);
                    close stack(stack, elems);
                } else {
                    {
                        predicate_family_instance stack_try_pop_operation_pre(operation)(struct stack *stack2) =
                            stack2 == stack &*&
                            is_atomic_load_pointer_operation(op) &*& 
                            atomic_load_pointer_operation_pre(op)(pp, prophecy);
                        predicate_family_instance stack_try_pop_operation_post(operation)(bool succes2, void* result2) =
                            is_atomic_load_pointer_operation(op) &*& 
                            atomic_load_pointer_operation_post(op)() &*&
                            succes2 == false &*&
                            result2 == 0;
                        lemma void operation() : stack_try_pop_operation
                            requires stack_try_pop_operation_pre(operation)(?stack2) &*& stack(stack2, ?elems);
                            ensures stack_try_pop_operation_post(operation)(elems != nil, head_or(elems, 0)) &*& 
                                stack(stack2, tail(elems));
                        {
                            open stack_try_pop_operation_pre(operation)(stack2);
                            open stack(stack, elems);
                            op();
                            open lseg(hProphecy, 0, _, _);
                            close lseg(hProphecy, 0, _, _);
                            close stack(stack, elems);
                            close stack_try_pop_operation_post(operation)(elems != nil, head_or(elems, 0));
                        }
                        close stack_try_pop_operation_pre(operation)(stack);
                        produce_lemma_function_pointer_chunk(operation) {
                            context(operation);
                        }
                        open stack_try_pop_operation_post(operation)(_, _);
                    }
                }
                unsep();
                close stack_inv_info(args, stack, inv, sep, unsep);
                close atomic_load_pointer_context_post(icontext)();
            }
            @*/
            //@ close atomic_load_pointer_context_pre(icontext)(inv, &stack->head, hProphecy);
            //@ produce_lemma_function_pointer_chunk(icontext);
            h = atomic_load_pointer(&stack->head);
            //@ open atomic_load_pointer_context_post(icontext)();
            //@ leak is_atomic_load_pointer_context(icontext);
        }
        if(h == 0) {
            succeeded = true;
            success = false;
            result = 0;
        } else {
            //@ open [?d]node(h, ?hn, ?hd);
            struct node *next = h->next;
            result = h->data;
            //@ close [d]node(h, next, result);
                        
            struct node *casResult; 
            //@ struct node *casResultProphecy = create_prophecy_pointer();
            {
                /*@
                predicate_family_instance atomic_compare_and_store_pointer_context_pre(icontext)(predicate() iinv, void **pp, void *old, void *new, void *prophecy) = 
                    iinv == inv &*& pp == &stack->head &*& old == h &*& new == next &*& prophecy == casResultProphecy &*& //end of argument fixing
                    [_]node(h, next, result) &*& 
                    h != 0 &*&
                    is_stack_try_pop_context(context) &*&
                    stack_inv_info(args, stack, inv, sep, unsep) &*&
                    stack_try_pop_context_pre(context)(unsep, stack, args);                     
                predicate_family_instance atomic_compare_and_store_pointer_context_post(icontext)() = 
                    is_stack_try_pop_context(context) &*&
                    stack_inv_info(args, stack, inv, sep, unsep) &*&
                    ( casResultProphecy == h ? 
                        stack_try_pop_context_post(context)(true, result, args) : 
                        stack_try_pop_context_pre(context)(unsep, stack, args));
                lemma void icontext(atomic_compare_and_store_pointer_operation *op):atomic_compare_and_store_pointer_context
                    requires
                        atomic_compare_and_store_pointer_context_pre(icontext)(?iinv, ?pp, ?old, ?new, ?prophecy) &*& iinv() &*&
                        is_atomic_compare_and_store_pointer_operation(op) &*&
                        atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
                    ensures
                        atomic_compare_and_store_pointer_context_post(icontext)() &*& iinv() &*&
                        is_atomic_compare_and_store_pointer_operation(op) &*&
                        atomic_compare_and_store_pointer_operation_post(op)();
                {
                    open atomic_compare_and_store_pointer_context_pre(icontext)(iinv, pp, old, new, prophecy);
                    open stack_inv_info(args, stack, inv, sep, unsep);
                    sep();
                    if(casResultProphecy == h) {
                        {
                            predicate_family_instance stack_try_pop_operation_pre(operation)(struct stack *stack2) =
                                stack2 == stack &*&
                                [_]node(h, next, result) &*&
                                is_atomic_compare_and_store_pointer_operation(op) &*&
                                atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
                            predicate_family_instance stack_try_pop_operation_post(operation)(bool succes2, void* result2) =
                                is_atomic_compare_and_store_pointer_operation(op) &*&
                                atomic_compare_and_store_pointer_operation_post(op)() &*&
                                succes2 == true &*&
                                result2 == result;
                            lemma void operation() : stack_try_pop_operation
                                requires stack_try_pop_operation_pre(operation)(?stack2) &*& stack(stack2, ?elems);
                                ensures stack_try_pop_operation_post(operation)(elems != nil, head_or(elems, 0)) &*& 
                                    stack(stack2, tail(elems));
                            {
                                open stack_try_pop_operation_pre(operation)(stack2);
                                open stack(stack, _);
                                struct node* head = stack->head;
                                op();
                                open lseg(head, 0, ?nodes, elems);
                                assert [_]node(head, ?headNext, ?headData);
                                assert headNext == next;
                                assert headData == result;
                                close stack(stack, _);
                                close stack_try_pop_operation_post(operation)(true, result); 
                            }
                            close stack_try_pop_operation_pre(operation)(stack);
                            produce_lemma_function_pointer_chunk(operation) {
                                context(operation);
                            }
                            open stack_try_pop_operation_post(operation)(_, _);
                        }
                    } else {
                        open stack(stack, _);
                        op();
                        close stack(stack, _);
                    } 
                    unsep();
                    close stack_inv_info(args, stack, inv, sep, unsep);
                    close atomic_compare_and_store_pointer_context_post(icontext)();
                }
                @*/
                //@ close atomic_compare_and_store_pointer_context_pre(icontext)(inv, &stack->head, h, next, casResultProphecy);
                //@ produce_lemma_function_pointer_chunk(icontext);
                casResult = atomic_compare_and_store_pointer(&stack->head, h, next);
                //@ open atomic_compare_and_store_pointer_context_post(icontext)();
                //@ leak is_atomic_compare_and_store_pointer_context(icontext);
            }
            succeeded = (casResult == h);
            success = true;
        }
    }
    *resultRef = result;
    return success;
}



void stack_push_sequential(struct stack *stack, void *data)
    //@ requires stack(stack, ?elems);
    //@ ensures stack(stack, cons(data, elems));
{
    //@ open stack(stack, elems);
    struct node *head = stack->head;
    struct node *node = malloc(sizeof(struct node));
    if (node == 0) abort();
    node->data = data;
    node->next = head;
    stack->head = node;
    //@ close node(node, head, data);
    //@ leak node(node, head, data);
    //@ close lseg(node, 0, _, _);
    //@ close stack(stack, cons(data, elems));
}

bool stack_try_pop_sequential(struct stack *stack, void** resultRef)
    //@ requires stack(stack, ?elems) &*& pointer(resultRef, _);
    //@ ensures stack(stack, tail(elems)) &*& pointer(resultRef, head_or(elems, 0)) &*& result == (elems != nil);
{
    //@ open stack(stack, elems);
    struct node* head = stack->head;
    //@ open lseg(head, 0, _, _);
    if(head == 0) {
        *resultRef = 0;
        //@ close stack(stack, tail(elems));
        return false;
    } else {
        void* data = head->data;
        struct node* next = head->next;
        stack->head = next;
        *resultRef = data;
        //@ close stack(stack, tail(elems));
        return true;
    }
            
}


//sharing lemma's 

/*@

lemma void share_stack(struct stack *stack)
    requires 
        stack(stack, ?elems) &*&
        is_stack_sep(?sep) &*&
        is_stack_unsep(?unsep) &*&
        stack_unsep(unsep)(?info, stack, ?inv, sep, elems);
    ensures atomic_space(inv) &*& stack_inv_info(info, stack, inv, sep, unsep);
{
    unsep();
    create_atomic_space(inv);
    close stack_inv_info(info, stack, inv, sep, unsep);
}

lemma void unshare_stack(struct stack *stack)
    requires atomic_space(?inv) &*& stack_inv_info(?info, stack, inv, ?sep, ?unsep); 
    ensures stack(stack, ?elems) &*&
        is_stack_sep(sep) &*&
        is_stack_unsep(unsep) &*&
        stack_unsep(unsep)(info, stack, inv, sep, elems);
{
    dispose_atomic_space(inv);
    open stack_inv_info(info, stack, inv, sep, unsep);
    sep();
}

@*/
