#include "stdlib.h"
#include "atomics.h"

/*
   A mutex based on atomic operations
   
   Another example to explain the use of atomics 
*/
struct mutex {
    void* locked;
    //@ predicate() p;
    //@ void* perm2;
    //@ real perm2frac;
};

/*@
predicate_ctor mutex_inv(struct mutex *mutex, predicate() p)() = 
    [1/2]mutex->p |-> p &*&
    [1/2]mutex->locked |-> ?locked &*& 
    [1/2]mutex->perm2frac |-> ?f &*& 
    (locked == (void*)1 ? 
        [f]mutex->perm2 |-> _ : 
        p() &*& locked == 0 &*& [1/2]mutex->locked |-> _ &*& [1/2]mutex->perm2frac |-> _);


predicate mutex_internal(struct mutex *mutex; predicate() p) =
    malloc_block_mutex(mutex) &*&
    [1/2]mutex->p |-> p &*&
    atomic_space(mutex_inv(mutex, p));

predicate mutex(struct mutex *mutex; predicate() p) =
    mutex_internal(mutex, p) &*&
    mutex->perm2 |-> _;
    
predicate mutex_held(struct mutex *mutex, predicate() p, int threadId, real frac) =
    [frac]mutex_internal(mutex, p) &*& 
    [1/2]mutex->locked |-> (void*)1 &*& 
    [1/2]mutex->perm2frac |-> frac;

predicate create_mutex_ghost_arg(predicate() p) = true;

@*/

struct mutex *create_mutex()
    //@ requires create_mutex_ghost_arg(?p) &*& p();
    //@ ensures mutex(result, p);
{
    //@ open create_mutex_ghost_arg(p);
    struct mutex* result = malloc(sizeof(struct mutex));
    if(result == 0) abort();
    result->locked = 0;
    //@ result->p = p;
    //@ close mutex_inv(result, p)();
    //@ create_atomic_space(mutex_inv(result, p));
    //@ close mutex(result, p);
    return result;
}
void mutex_acquire(struct mutex *mutex)
    //@ requires [?f]mutex(mutex, ?p);
    //@ ensures mutex_held(mutex, p, currentThread, f) &*& p();
{
    bool succeeded = false;
    while(!succeeded)
    //@ invariant succeeded ? mutex_held(mutex, p, currentThread, f) &*& p() : [f]mutex(mutex, p);
    {
        void* casresult; 
        //@ void *lockedProphecy = create_prophecy_pointer();
        {
            /*@
                predicate_family_instance atomic_compare_and_store_pointer_context_pre(ctxt)(predicate() inv, void **pp, void *old, void *new, void *prophecy) =
                    inv == mutex_inv(mutex, p) &*& 
                    pp == &mutex->locked &*& 
                    old == 0 &*& 
                    new == (void*)1 &*& 
                    prophecy == lockedProphecy &*&
                    [f]mutex->perm2 |-> _;
                predicate_family_instance atomic_compare_and_store_pointer_context_post(ctxt)() =
                    lockedProphecy == 0 ? p() &*& [1/2]mutex->locked |-> (void*)1 &*& [1/2]mutex->perm2frac |-> f : [f]mutex->perm2 |-> _;
                lemma void ctxt(atomic_compare_and_store_pointer_operation *op) : atomic_compare_and_store_pointer_context
                    requires
                        atomic_compare_and_store_pointer_context_pre(ctxt)(?inv, ?pp, ?old, ?new, ?prophecy) &*& inv() &*&
                        is_atomic_compare_and_store_pointer_operation(op) &*&
                        atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
                    ensures
                        atomic_compare_and_store_pointer_context_post(ctxt)() &*& inv() &*&
                        is_atomic_compare_and_store_pointer_operation(op) &*&
                        atomic_compare_and_store_pointer_operation_post(op)();
            {
                open atomic_compare_and_store_pointer_context_pre(ctxt)(inv, pp, old, new, prophecy);
                open mutex_inv(mutex, p)();
                op();
                if(lockedProphecy == 0) mutex->perm2frac = f;
                close mutex_inv(mutex, p)();
                close atomic_compare_and_store_pointer_context_post(ctxt)();
            }
        @*/
            //@ open mutex(mutex, p);
            //@ open mutex_internal(mutex, p);
            //@ close atomic_compare_and_store_pointer_context_pre(ctxt)(mutex_inv(mutex, p), &mutex->locked, 0, (void*)1, lockedProphecy);
            //@ produce_lemma_function_pointer_chunk(ctxt);
            casresult = atomic_compare_and_store_pointer(&mutex->locked, 0, (void*)1);
            //@ open atomic_compare_and_store_pointer_context_post(ctxt)();
            //@ leak is_atomic_compare_and_store_pointer_context(ctxt);
            //@ close [f]mutex_internal(mutex, p);
        }
        succeeded = (casresult == 0);
        //@ if(succeeded) close mutex_held(mutex, p, currentThread, f); else close [f]mutex(mutex, p);
    }
}
void mutex_release(struct mutex *mutex)
    //@ requires mutex_held(mutex, ?p, currentThread, ?f) &*& p();
    //@ ensures [f]mutex(mutex, p);
{
        //@ open mutex_held(mutex, p, currentThread, f);
        //@ open [f]mutex_internal(mutex, p);
        {
            /*@
                predicate_family_instance atomic_store_pointer_context_pre(ctxt)(predicate() inv, void **pp, void *new) =
                    inv == mutex_inv(mutex, p) &*& pp == &mutex->locked &*& new == (void*)0 &*& p() &*& [1/2]mutex->locked |-> (void*)1 &*& [1/2]mutex->perm2frac |-> f;
                predicate_family_instance atomic_store_pointer_context_post(ctxt)() =
                    [f]mutex->perm2 |-> _;
                lemma void ctxt(atomic_store_pointer_operation *op) : atomic_store_pointer_context
                    requires
                        atomic_store_pointer_context_pre(ctxt)(?inv, ?pp, ?new) &*& inv() &*&
                        is_atomic_store_pointer_operation(op) &*&
                        atomic_store_pointer_operation_pre(op)(pp, new);
                    ensures
                        atomic_store_pointer_context_post(ctxt)() &*& inv() &*&
                        is_atomic_store_pointer_operation(op) &*&
                        atomic_store_pointer_operation_post(op)();
            {
                open atomic_store_pointer_context_pre(ctxt)(inv, pp, new);
                open mutex_inv(mutex, p)();
                void* locked = mutex->locked;
                assert locked != 0;
                op();
                close mutex_inv(mutex, p)();
                close atomic_store_pointer_context_post(ctxt)();
            }
        @*/
            //@ close atomic_store_pointer_context_pre(ctxt)(mutex_inv(mutex, p), &mutex->locked, 0);
            //@ produce_lemma_function_pointer_chunk(ctxt);
            atomic_store_pointer(&mutex->locked, 0);
            //@ open atomic_store_pointer_context_post(ctxt)();
            //@ leak is_atomic_store_pointer_context(ctxt);
            //@ close [f]mutex(mutex, p);
        }
}
void mutex_dispose(struct mutex *mutex)
    //@ requires mutex(mutex, ?p);
    //@ ensures p();
{
    //@ open mutex(mutex, p);
    //@ open mutex_internal(mutex, p);
    //@ dispose_atomic_space(mutex_inv(mutex, p));
    //@ open mutex_inv(mutex, p)();
    free(mutex);
}
