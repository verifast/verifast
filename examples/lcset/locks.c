#include "atomics.h"
#include "locks.h"

void lock(void **lock)
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_lock_context(?ctxt) &*& lock_context_pre(ctxt)(inv, lock);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_lock_context(ctxt) &*& lock_context_post(ctxt)();
    @*/
{
loop:
    //@ invariant [f]atomic_space(inv) &*& is_lock_context(ctxt) &*& lock_context_pre(ctxt)(inv, lock);
    prophecy_id prophecyId = create_prophecy_pointer();
    //@ assert prophecy_pointer(prophecyId, ?prophecy);
    {
        /*@
        predicate_family_instance atomic_compare_and_store_pointer_context_pre(context)(predicate() inv_, void **pp, void *old, void *new, void *prophecy_) =
            inv_ == inv &*& pp == lock &*& old == 0 &*& new == (void *)1 &*& prophecy_ == prophecy &*&
            is_lock_context(ctxt) &*& lock_context_pre(ctxt)(inv, lock);
        predicate_family_instance atomic_compare_and_store_pointer_context_post(context)() =
            is_lock_context(ctxt) &*& prophecy == 0 ? lock_context_post(ctxt)() : lock_context_pre(ctxt)(inv, lock);
        lemma void context(atomic_compare_and_store_pointer_operation *op) : atomic_compare_and_store_pointer_context
            requires
                atomic_compare_and_store_pointer_context_pre(context)(?inv_, ?pp, ?old, ?new, ?prophecy_) &*& inv_() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*& atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy_);
            ensures
                atomic_compare_and_store_pointer_context_post(context)() &*& inv_() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*& atomic_compare_and_store_pointer_operation_post(op)();
        {
            open atomic_compare_and_store_pointer_context_pre(context)(_, _, _, _, _);
            {
                predicate_family_instance lock_operation_pre(lop)(void **lock_) =
                    lock_ == lock &*&
                    is_atomic_compare_and_store_pointer_operation(op) &*& atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy_);
                predicate_family_instance lock_operation_post(lop)(bool success) =
                    success == (prophecy == 0) &*&
                    is_atomic_compare_and_store_pointer_operation(op) &*& atomic_compare_and_store_pointer_operation_post(op)();
                lemma void lop() : lock_operation
                    requires lock_operation_pre(lop)(?lock_) &*& [?fPointer]pointer(lock_, ?value) &*& value == 0 ? fPointer == 1 : true;
                    ensures lock_operation_post(lop)(value == 0) &*& [fPointer]pointer(lock_, value == 0 ? (void *)1 : value);
                {
                    open lock_operation_pre(lop)(_);
                    op();
                    close lock_operation_post(lop)(value == 0);
                }
                close lock_operation_pre(lop)(lock);
                produce_lemma_function_pointer_chunk(lop) {
                    ctxt(lop);
                }
                open lock_operation_post(lop)(_);
            }
            close atomic_compare_and_store_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_compare_and_store_pointer_context_pre(context)(inv, lock, 0, (void *)1, prophecy);
        //@ produce_lemma_function_pointer_chunk(context);
        void *v = atomic_compare_and_store_pointer(prophecyId, lock, 0, (void *)1);
        //@ leak is_atomic_compare_and_store_pointer_context(context);
        //@ open atomic_compare_and_store_pointer_context_post(context)();
        if (v != 0) goto loop;
    }
}

void unlock(void **lock)
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_atomic_store_pointer_context(?ctxt) &*& atomic_store_pointer_context_pre(ctxt)(inv, lock, 0);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_store_pointer_context(ctxt) &*& atomic_store_pointer_context_post(ctxt)();
    @*/
{
    atomic_store_pointer(lock, 0);
}
