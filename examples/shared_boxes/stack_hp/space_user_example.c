#include "atomics.h"
//@ #include "space_user.gh"

/*

This example shows how you can make sure that an atomic space can not be disposed before 
it has no more users left.

*/

/*@

predicate_ctor space_inv(int id)() = 
    space_user_info(id, ?count);

predicate_family_instance space_user_info_sep  (space_inv_sep)  (any args, int id, predicate() inv, space_user_info_unsep *unsep) = 
    inv == space_inv(id) &*& 
    unsep == space_inv_unsep;
predicate_family_instance space_user_info_unsep(space_inv_unsep)(any args, int id, predicate() inv, space_user_info_sep *sep, int count) = 
    inv == space_inv(id) &*& 
    sep == space_inv_sep;

lemma void space_inv_sep() : space_user_info_sep
    requires space_user_info_sep(space_inv_sep)(?args, ?id, ?inv, ?unsep) &*& inv();
    ensures space_user_info_unsep(unsep)(args, id, inv, space_inv_sep, ?count) &*& space_user_info(id, count);
{
    open space_user_info_sep(space_inv_sep)(args, id, inv, unsep);
    open space_inv(id)();
    assert space_user_info(id, ?count);
    close space_user_info_unsep(space_inv_unsep)(args, id, inv, space_inv_sep, count);
}
lemma void space_inv_unsep() : space_user_info_unsep
    requires space_user_info_unsep(space_inv_unsep)(?args, ?id, ?inv, ?sep, ?count) &*& space_user_info(id, count);
    ensures space_user_info_sep(sep)(args, id, inv, space_inv_unsep) &*& inv();
{
    open space_user_info_unsep(space_inv_unsep)(args, id, inv, sep, count);
    close space_inv(id)();
    close space_user_info_sep(space_inv_sep)(args, id, inv, space_inv_unsep);
}

@*/


void test_create()
//@ requires true;
//@ ensures dispose_perm(?id) &*& atomic_space(space_inv(id));
{
    //@ space_user_info_create();
    //@ assert space_user_info(?sid, 0);
    //@ close space_inv(sid)();
    //@ create_atomic_space(space_inv(sid));
}


void test_dispose()
//@ requires dispose_perm(?id) &*& atomic_space(space_inv(id));
//@ ensures true;
{
    //@ dispose_atomic_space(space_inv(id));
    //@ open space_inv(id)();
    //@ space_user_info_dispose(id);
    
}


void test_acquire()
//@ requires [?f]dispose_perm(?id) &*& [?f2]atomic_space(space_inv(id));
//@ ensures space_user(id, f) &*& [f2]atomic_space(space_inv(id));
{
    { 
        /*@
         predicate_family_instance atomic_noop_context_pre(context_lemma)(predicate() inv) = 
             inv == space_inv(id) &*&
             [f]dispose_perm(id);
         predicate_family_instance atomic_noop_context_post(context_lemma)() = 
             space_user(id, f);
         lemma void context_lemma() : atomic_noop_context()
             requires atomic_noop_context_pre(context_lemma)(?inv) &*& inv();
             ensures atomic_noop_context_post(context_lemma)() &*& inv();
         {
             open atomic_noop_context_pre(context_lemma)(inv);
             open space_inv(id)();
             space_user_info_add_user(id, f);
             close space_inv(id)();
             close atomic_noop_context_post(context_lemma)();
         }
         @*/
         //@ close atomic_noop_context_pre(context_lemma)(space_inv(id));
        //@ produce_lemma_function_pointer_chunk(context_lemma);
         atomic_noop();
         //@ leak is_atomic_noop_context(context_lemma);
         //@ open atomic_noop_context_post(context_lemma)();
    }
}


void test_release()
//@ requires space_user(?id, ?f) &*& [?f2]atomic_space(space_inv(id));
//@ ensures [f]dispose_perm(id) &*& [f2]atomic_space(space_inv(id));
{
    { 
        /*@
         predicate_family_instance atomic_noop_context_pre(context_lemma)(predicate() inv) = 
             inv == space_inv(id) &*&
             space_user(id, f);
         predicate_family_instance atomic_noop_context_post(context_lemma)() = 
             [f]dispose_perm(id);
         lemma void context_lemma() : atomic_noop_context()
             requires atomic_noop_context_pre(context_lemma)(?inv) &*& inv();
             ensures atomic_noop_context_post(context_lemma)() &*& inv();
         {
             open atomic_noop_context_pre(context_lemma)(inv);
             open space_inv(id)();
             space_user_info_remove_user(id, f);
             close space_inv(id)();
             close atomic_noop_context_post(context_lemma)();
         }
         @*/
         //@ close atomic_noop_context_pre(context_lemma)(space_inv(id));
        //@ produce_lemma_function_pointer_chunk(context_lemma);
         atomic_noop();
         //@ leak is_atomic_noop_context(context_lemma);
         //@ open atomic_noop_context_post(context_lemma)();
    }
}

