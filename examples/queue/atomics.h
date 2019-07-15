#ifndef ATOMICS_H
#define ATOMICS_H

/*@

predicate atomic_space(predicate() inv);

lemma void create_atomic_space(predicate() inv);
    requires inv();
    ensures atomic_space(inv);

lemma void dispose_atomic_space(predicate() inv);
    requires atomic_space(inv);
    ensures inv();
    
@*/

/*@

typedef lemma void atomic_load_pointer_operation(void **pp, predicate() P, predicate(void *) Q)();
    requires pointer(pp, ?p) &*& P();
    ensures pointer(pp, p) &*& Q(p);

typedef lemma void atomic_load_pointer_context(predicate() inv, void **pp, predicate() pre, predicate(void *) post)();
    requires inv() &*& is_atomic_load_pointer_operation(?op, pp, ?P, ?Q) &*& P() &*& pre();
    ensures inv() &*& is_atomic_load_pointer_operation(op, pp, P, Q) &*& Q(?p) &*& post(p);

@*/

void *atomic_load_pointer(void **pp);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_atomic_load_pointer_context(?ctxt, inv, pp, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_load_pointer_context(ctxt, inv, pp, pre, post) &*& post(result);
    @*/

/*@

typedef lemma bool atomic_compare_and_store_pointer_operation(void **pp, void *old, void *new, predicate() P, predicate(bool) Q)();
    requires pointer(pp, ?p0) &*& P();
    ensures pointer(pp, ?p1) &*& Q(result) &*& result ? p0 == old && p1 == new : p1 == p0;

typedef lemma void atomic_compare_and_store_pointer_context(predicate() inv, void **pp, void *old, void *new, predicate() pre, predicate(bool) post)();
    requires
        inv() &*&
        is_atomic_compare_and_store_pointer_operation(?op, pp, old, new, ?P, ?Q) &*& P() &*& pre();
    ensures
        inv() &*&
        is_atomic_compare_and_store_pointer_operation(op, pp, old, new, P, Q) &*& Q(?result) &*& post(result);

@*/

bool atomic_compare_and_store_pointer(void **pp, void *old, void *new);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_atomic_compare_and_store_pointer_context(?ctxt, inv, pp, old, new, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_compare_and_store_pointer_context(ctxt, inv, pp, old, new, pre, post) &*& post(result);
    @*/

/*@

typedef lemma void atomic_noop_context(predicate() inv, predicate() pre, predicate() post)();
    requires inv() &*& pre();
    ensures inv() &*& post();

@*/

void atomic_noop();
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_atomic_noop_context(?ctxt, inv, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_noop_context(ctxt, inv, pre, post) &*& post();
    @*/

#endif