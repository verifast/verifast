#include "stdlib.h"
#include "atomics.h"
//@ #include "fraction_store.gh"

/*
   A mutex based on atomic operations
   
   We are using a fraction store to 
   Another example to explain the use of atomics 
*/
struct mutex {
    void* locked;
    //@ predicate() p;
    //@ int fsId;
    //@ unit perm2;
};

/*@

predicate fs_helper(struct mutex *mutex; unit u) = mutex->perm2 |-> u;

predicate_ctor mutex_inv(struct mutex *mutex, predicate() p, int fsId)() = 
    [1/2]mutex->p |-> p &*&
    [1/2]mutex->locked |-> ?locked &*& 
    fraction_store(fsId, fs_helper, mutex, ?c, ?r) &*&
    (locked == (void*)1 ? 
        c == 1 : 
        p() &*& locked == 0 &*& [1/2]mutex->locked |-> _ &*& c == 0);


predicate mutex_internal(struct mutex *mutex; predicate() p, int fsId) =
    malloc_block_mutex(mutex) &*&
    [1/2]mutex->p |-> p &*&
    mutex->fsId |-> fsId &*&
    atomic_space(mutex_inv(mutex, p, fsId));

predicate mutex(struct mutex *mutex; predicate() p) =
    mutex_internal(mutex, p, ?fsId) &*&
    fs_helper(mutex, _);
    
predicate mutex_held(struct mutex *mutex, predicate() p, int threadId, real frac) =
    [frac]mutex_internal(mutex, p, ?fsId) &*& 
    fraction_store_ticket<struct mutex*, unit>(fsId, frac) &*&
    [1/2]mutex->locked |-> (void*)1;

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
    //@ result->perm2 = unit;
    //@ close fs_helper(result, unit);
    //@ result->p = p;
    //@ int fsId = create_fraction_store(fs_helper, result);
    //@ result->fsId = fsId;
    //@ close mutex_inv(result, p, fsId)();
    //@ create_atomic_space(mutex_inv(result, p, fsId));
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
        //@ open mutex(mutex, p);
        //@ open mutex_internal(mutex, p, ?fsId);
            
        void* casresult; 
        //@ void *lockedProphecy = create_prophecy_pointer();
        {
            /*@
                predicate_family_instance atomic_compare_and_store_pointer_context_pre(ctxt)(predicate() inv, void **pp, void *old, void *new, void *prophecy) =
                    inv == mutex_inv(mutex, p, fsId) &*& 
                    pp == &mutex->locked &*& 
                    old == 0 &*& 
                    new == (void*)1 &*& 
                    prophecy == lockedProphecy &*&
                    [f]fs_helper(mutex, _);
                predicate_family_instance atomic_compare_and_store_pointer_context_post(ctxt)() =
                    lockedProphecy == 0 ? p() &*& [1/2]mutex->locked |-> (void*)1 &*& fraction_store_ticket<struct mutex*, unit>(fsId, f) : [f]fs_helper(mutex, _);
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
                open mutex_inv(mutex, p, fsId)();
                op();
                if(lockedProphecy == 0) fraction_store_deposit(fsId, f);
                close mutex_inv(mutex, p, fsId)();
                close atomic_compare_and_store_pointer_context_post(ctxt)();
            }
        @*/
            //@ close atomic_compare_and_store_pointer_context_pre(ctxt)(mutex_inv(mutex, p, fsId), &mutex->locked, 0, (void*)1, lockedProphecy);
            //@ produce_lemma_function_pointer_chunk(ctxt);
            casresult = atomic_compare_and_store_pointer(&mutex->locked, 0, (void*)1);
            //@ open atomic_compare_and_store_pointer_context_post(ctxt)();
            //@ leak is_atomic_compare_and_store_pointer_context(ctxt);
        }
        succeeded = (casresult == 0);
        //@ close [f]mutex_internal(mutex, p, fsId);
        //@ if(succeeded) close mutex_held(mutex, p, currentThread, f); else close [f]mutex(mutex, p);
    }
}
void mutex_release(struct mutex *mutex)
    //@ requires mutex_held(mutex, ?p, currentThread, ?f) &*& p();
    //@ ensures [f]mutex(mutex, p);
{
        //@ open mutex_held(mutex, p, currentThread, f);
        //@ open [f]mutex_internal(mutex, p, ?fsId);
        {
            /*@
                predicate_family_instance atomic_store_pointer_context_pre(ctxt)(predicate() inv, void **pp, void *new) =
                    inv == mutex_inv(mutex, p, fsId) &*& 
                    pp == &mutex->locked &*& 
                    new == (void*)0 &*& p() &*& 
                    [1/2]mutex->locked |-> (void*)1 &*& 
                    fraction_store_ticket<struct mutex*, unit>(fsId, f);
                predicate_family_instance atomic_store_pointer_context_post(ctxt)() =
                    [f]fs_helper(mutex, _);
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
                open mutex_inv(mutex, p, fsId)();
                void* locked = mutex->locked;
                assert locked != 0;
                fraction_store_withdraw(fsId, f);
                op();
                close mutex_inv(mutex, p, fsId)();
                close atomic_store_pointer_context_post(ctxt)();
            }
        @*/
            //@ close atomic_store_pointer_context_pre(ctxt)(mutex_inv(mutex, p, fsId), &mutex->locked, 0);
            //@ produce_lemma_function_pointer_chunk(ctxt);
            atomic_store_pointer(&mutex->locked, 0);
            //@ open atomic_store_pointer_context_post(ctxt)();
            //@ leak is_atomic_store_pointer_context(ctxt);
            //@ close [f]mutex(mutex, p);
        }
}
/*@
lemma void fs_helper_unique(struct mutex* m)
    requires [?f]fs_helper(m, ?b);
    ensures [f]fs_helper(m, b) &*& f <= 1;
{
    if(f>=1) {
        open [f] fs_helper(m, _);
        close [1/2] fs_helper(m, _);
        open [1/2] fs_helper(m, _);
    }
}
@*/
void mutex_dispose(struct mutex *mutex)
    //@ requires mutex(mutex, ?p);
    //@ ensures p();
{
    //@ open mutex(mutex, p);
    //@ open mutex_internal(mutex, p, ?fsId);
    //@ dispose_atomic_space(mutex_inv(mutex, p, fsId));
    //@ open mutex_inv(mutex, p, fsId)();
    /*@ 
        produce_lemma_function_pointer_chunk(fs_helper_unique) 
            : predicate_unique<struct mutex*, unit>(fs_helper)(arg1) { call(); } 
        {
            fraction_store_unique_empty(fsId);
        }
    @*/
    //@ fraction_store_dispose(fsId);
    free(mutex);
}
