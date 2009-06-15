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

predicate atomic_load_pointer_operation_pre(void *pp);
predicate atomic_load_pointer_operation_post(void *p);

typedef lemma void atomic_load_pointer_operation();
    requires atomic_load_pointer_operation_pre(?pp) &*& pointer(pp, ?p);
    ensures atomic_load_pointer_operation_post(p) &*& pointer(pp, p);

predicate_family atomic_load_pointer_context_pre(void *ctxt)(any info, predicate() inv, void **pp);
predicate_family atomic_load_pointer_context_post(void *ctxt)(any info, void *p);

typedef lemma void atomic_load_pointer_context(atomic_load_pointer_operation *op);
    requires
        atomic_load_pointer_context_pre(this)(?info, ?inv, ?pp) &*& inv() &*&
        is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(pp);
    ensures
        atomic_load_pointer_context_post(this)(info, ?p) &*& inv() &*&
        is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(p);

predicate atomic_load_pointer_ghost_arg(atomic_load_pointer_context *ctxt) = true;

@*/

void *atomic_load_pointer(void **pp);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        atomic_load_pointer_ghost_arg(?ctxt) &*&
        is_atomic_load_pointer_context(ctxt) &*&
        atomic_load_pointer_context_pre(ctxt)(?info, inv, pp);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_load_pointer_context(ctxt) &*&
        atomic_load_pointer_context_post(ctxt)(info, result);
    @*/

/*@

predicate atomic_compare_and_store_pointer_operation_pre(void **pp, void *old, void *new);
predicate atomic_compare_and_store_pointer_operation_post(bool result);

typedef lemma bool atomic_compare_and_store_pointer_operation();
    requires atomic_compare_and_store_pointer_operation_pre(?pp, ?old, ?new) &*& pointer(pp, ?p0);
    ensures atomic_compare_and_store_pointer_operation_post(result) &*& pointer(pp, ?p1) &*& result ? p0 == old && p1 == new : p1 == p0;

predicate_family atomic_compare_and_store_pointer_context_pre(void *ctxt)(any info, predicate() inv, void **pp, void *old, void *new);
predicate_family atomic_compare_and_store_pointer_context_post(void *ctxt)(any info, bool result);

typedef lemma void atomic_compare_and_store_pointer_context(atomic_compare_and_store_pointer_operation *op);
    requires
        atomic_compare_and_store_pointer_context_pre(this)(?info, ?inv, ?pp, ?old, ?new) &*& inv() &*&
        is_atomic_compare_and_store_pointer_operation(op) &*&
        atomic_compare_and_store_pointer_operation_pre(pp, old, new);
    ensures
        atomic_compare_and_store_pointer_context_post(this)(info, ?result) &*& inv() &*&
        is_atomic_compare_and_store_pointer_operation(op) &*&
        atomic_compare_and_store_pointer_operation_post(result);

predicate atomic_compare_and_store_pointer_ghost_arg(atomic_compare_and_store_pointer_context *ctxt) = true;

@*/

bool atomic_compare_and_store_pointer(void **pp, void *old, void *new);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        atomic_compare_and_store_pointer_ghost_arg(?ctxt) &*&
        is_atomic_compare_and_store_pointer_context(ctxt) &*&
        atomic_compare_and_store_pointer_context_pre(ctxt)(?info, inv, pp, old, new);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_compare_and_store_pointer_context(ctxt) &*&
        atomic_compare_and_store_pointer_context_post(ctxt)(info, result);
    @*/

/*@

predicate_family atomic_noop_context_pre(void *ctxt)(any info, predicate() inv);
predicate_family atomic_noop_context_post(void *ctxt)(any info);

typedef lemma void atomic_noop_context();
    requires atomic_noop_context_pre(this)(?info, ?inv) &*& inv();
    ensures atomic_noop_context_post(this)(info) &*& inv();

predicate atomic_noop_ghost_arg(atomic_noop_context *ctxt) = true;

@*/

void atomic_noop();
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        atomic_noop_ghost_arg(?ctxt) &*&
        is_atomic_noop_context(ctxt) &*&
        atomic_noop_context_pre(ctxt)(?info, inv);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_noop_context(ctxt) &*&
        atomic_noop_context_post(ctxt)(info);
    @*/

#endif