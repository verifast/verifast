#ifndef ATOMICS_H
#define ATOMICS_H

// The idea of prophecies for verification of concurrent programs was introduced by [1].
// [1] Martin Abadi and Leslie Lamport. The existence of refinement mappings. Theoretical Computer Science 82(2), 1991.

/*@

predicate atomic_space(predicate() inv;);

lemma void create_atomic_space(predicate() inv);
    requires inv();
    ensures atomic_space(inv);

lemma void dispose_atomic_space(predicate() inv);
    requires atomic_space(inv);
    ensures inv();

predicate prophecy_pointer(void *prophecy);

lemma void *create_prophecy_pointer(); // FIXME: Unsound: Introduce explicit prophecy IDs (see e.g. examples/splitcounter)
    requires true;
    ensures prophecy_pointer(result);

predicate_family atomic_load_pointer_operation_pre(void *op)(void *pp, void *prophecy);
predicate_family atomic_load_pointer_operation_post(void *op)();

typedef lemma void atomic_load_pointer_operation();
    requires atomic_load_pointer_operation_pre(this)(?pp, ?prophecy) &*& [?f]pointer(pp, ?p);
    ensures atomic_load_pointer_operation_post(this)() &*& [f]pointer(pp, p) &*& p == prophecy;

predicate_family atomic_load_pointer_context_pre(void *ctxt)(predicate() inv, void **pp, void *prophecy);
predicate_family atomic_load_pointer_context_post(void *ctxt)();

typedef lemma void atomic_load_pointer_context(atomic_load_pointer_operation *op);
    requires
        atomic_load_pointer_context_pre(this)(?inv, ?pp, ?prophecy) &*& inv() &*&
        is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
    ensures
        atomic_load_pointer_context_post(this)() &*& inv() &*&
        is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();

@*/

void *atomic_load_pointer(void **pp);
    /*@
    requires
        [?f]atomic_space(?inv) &*& prophecy_pointer(?prophecy) &*&
        is_atomic_load_pointer_context(?ctxt) &*&
        atomic_load_pointer_context_pre(ctxt)(inv, pp, prophecy);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_load_pointer_context(ctxt) &*&
        atomic_load_pointer_context_post(ctxt)() &*&
        result == prophecy;
    @*/

/*@

predicate_family atomic_compare_and_store_pointer_operation_pre(void *op)(void **pp, void *old, void *new, void *prophecy);
predicate_family atomic_compare_and_store_pointer_operation_post(void *op)();

typedef lemma void atomic_compare_and_store_pointer_operation();
    requires
        atomic_compare_and_store_pointer_operation_pre(this)(?pp, ?old, ?new, ?prophecy) &*&
        [?f]pointer(pp, ?p0) &*& p0 == old ? f == 1 : true;
    ensures
        atomic_compare_and_store_pointer_operation_post(this)() &*&
        [f]pointer(pp, ?p1) &*& p0 == prophecy &*&
        p1 == (p0 == old ? new : p0);

predicate_family
    atomic_compare_and_store_pointer_context_pre
    (void *ctxt)(predicate() inv, void **pp, void *old, void *new, void *prophecy);
predicate_family atomic_compare_and_store_pointer_context_post(void *ctxt)();

typedef lemma void atomic_compare_and_store_pointer_context(atomic_compare_and_store_pointer_operation *op);
    requires
        atomic_compare_and_store_pointer_context_pre(this)(?inv, ?pp, ?old, ?new, ?prophecy) &*& inv() &*&
        is_atomic_compare_and_store_pointer_operation(op) &*&
        atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
    ensures
        atomic_compare_and_store_pointer_context_post(this)() &*& inv() &*&
        is_atomic_compare_and_store_pointer_operation(op) &*&
        atomic_compare_and_store_pointer_operation_post(op)();

@*/

void *atomic_compare_and_store_pointer(void **pp, void *old, void *new);
    /*@
    requires
        [?f]atomic_space(?inv) &*& prophecy_pointer(?prophecy) &*&
        is_atomic_compare_and_store_pointer_context(?ctxt) &*&
        atomic_compare_and_store_pointer_context_pre(ctxt)(inv, pp, old, new, prophecy);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_compare_and_store_pointer_context(ctxt) &*&
        atomic_compare_and_store_pointer_context_post(ctxt)() &*&
        result == prophecy;
    @*/

/*@

predicate_family atomic_noop_context_pre(void *ctxt)(predicate() inv);
predicate_family atomic_noop_context_post(void *ctxt)();

typedef lemma void atomic_noop_context();
    requires atomic_noop_context_pre(this)(?inv) &*& inv();
    ensures atomic_noop_context_post(this)() &*& inv();

@*/

void atomic_noop();
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_atomic_noop_context(?ctxt) &*&
        atomic_noop_context_pre(ctxt)(inv);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_noop_context(ctxt) &*&
        atomic_noop_context_post(ctxt)();
    @*/

struct cas_tracker;

//@ predicate cas_tracker(struct cas_tracker *tracker, int count);

struct cas_tracker *create_cas_tracker();
    //@ requires true;
    //@ ensures cas_tracker(result, 0);

/*@

predicate tracked_cas_prediction(struct cas_tracker *tracker, int count; void *value);

lemma void *create_tracked_cas_prediction(struct cas_tracker *tracker, int count);
    requires true;
    ensures [_]tracked_cas_prediction(tracker, count, result);

predicate_family tracked_cas_pre(void *op)(struct cas_tracker *tracker, void **pp, void *old, void *new, void *prophecy);
predicate_family tracked_cas_post(void *op)();

typedef lemma void tracked_cas_operation(int n, void *new0);
    requires
        tracked_cas_pre(this)(?tracker, ?pp, ?old, ?new, ?prophecy) &*&
        [?f]pointer(pp, ?p0) &*&
        p0 == prophecy ?
            p0 == old ?
                f == 1 &*& cas_tracker(tracker, n) &*& [_]tracked_cas_prediction(tracker, n, new0)
            :
                true
        :
            true;
    ensures
        tracked_cas_post(this)() &*&
        [f]pointer(pp, ?p1) &*& p0 == prophecy &*&
        p0 == old ? p1 == new &*& cas_tracker(tracker, n + 1) &*& new0 == new : p1 == p0;

predicate_family
    tracked_cas_ctxt_pre
    (void *ctxt)(struct cas_tracker *tracker, predicate() inv, void **pp, void *old, void *new, void *prophecy);
predicate_family tracked_cas_ctxt_post(void *ctxt)();

typedef lemma void tracked_cas_ctxt(tracked_cas_operation *op);
    requires
        tracked_cas_ctxt_pre(this)(?tracker, ?inv, ?pp, ?old, ?new, ?prophecy) &*& inv() &*&
        is_tracked_cas_operation(op) &*&
        tracked_cas_pre(op)(tracker, pp, old, new, prophecy);
    ensures
        tracked_cas_ctxt_post(this)() &*& inv() &*&
        is_tracked_cas_operation(op) &*&
        tracked_cas_post(op)();

@*/

void *tracked_cas(struct cas_tracker *tracker, void **pp, void *old, void *new);
    /*@
    requires
        [?f]atomic_space(?inv) &*& prophecy_pointer(?prophecy) &*&
        is_tracked_cas_ctxt(?ctxt) &*&
        tracked_cas_ctxt_pre(ctxt)(tracker, inv, pp, old, new, prophecy);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_tracked_cas_ctxt(ctxt) &*&
        tracked_cas_ctxt_post(ctxt)() &*&
        result == prophecy;
    @*/

/*@

predicate_family atomic_store_pointer_operation_pre(void *op)(void **pp, void *p);
predicate_family atomic_store_pointer_operation_post(void *op)();

typedef lemma void atomic_store_pointer_operation();
    requires atomic_store_pointer_operation_pre(this)(?pp, ?p) &*& pointer(pp, _);
    ensures atomic_store_pointer_operation_post(this)() &*& pointer(pp, p);

predicate_family atomic_store_pointer_context_pre(void *ctxt)(predicate() inv, void **pp, void *p);
predicate_family atomic_store_pointer_context_post(void *ctxt)();

typedef lemma void atomic_store_pointer_context(atomic_store_pointer_operation *op);
    requires
        atomic_store_pointer_context_pre(this)(?inv, ?pp, ?p) &*& inv() &*&
        is_atomic_store_pointer_operation(op) &*& atomic_store_pointer_operation_pre(op)(pp, p);
    ensures
        atomic_store_pointer_context_post(this)() &*& inv() &*&
        is_atomic_store_pointer_operation(op) &*& atomic_store_pointer_operation_post(op)();

@*/

void atomic_store_pointer(void **pp, void *p);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_atomic_store_pointer_context(?ctxt) &*& atomic_store_pointer_context_pre(ctxt)(inv, pp, p);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_store_pointer_context(ctxt) &*& atomic_store_pointer_context_post(ctxt)();
    @*/

#endif
