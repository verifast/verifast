#include "stdlib.h"
#include "atomics.h"
#include "rdcss.h"
//@ #include "bitops_ex.gh"
//@ #include "ghost_cells_ex.gh"
//@ #include "ghost_lists.gh"

// A port of the RDCSS [1] proof by Vafeiadis [2] to VeriFast
// [1] Tim Harris, Keir Fraser, and Ian A. Pratt. A practical multi-word compare-and-swap operation.
//     In 16th International Symposium on Distributed Computing, pages 265-279, October 2002.
// [2] Viktor Vafeiadis. Modular verification of fine-grained concurrency. PhD Thesis. Computer Laboratory, University of Cambridge. July 2008.

// As in [2], this version of the algorithm does not perform descriptor cleanup; i.e., a garbage collector is assumed.

struct rdcss_descriptor {
    void **a1;
    void *o1;
    void **a2;
    void *o2;
    void *n2;
    struct cas_tracker *tracker;
    //@ rdcss_operation_lemma *op;
    //@ bool done;
    //@ bool success;
    //@ bool detached;
    //@ bool disposed;
};

/*@

predicate rdcss_cell_frac(void **a, real frac) = true;

predicate_ctor rdcss_cell(int dsList)(void **a, void *v) =
    rdcss_cell_frac(a, ?f) &*&
    [f]pointer(a, ?w) &*&
    true == (((uintptr_t)w & 1) == 0) ?
        f == 1 &*& w == v
    :
        f == 1/2 &*&
        rdcss_cell_attached(dsList, (struct rdcss_descriptor *)((uintptr_t)w & ~1), a, v);

predicate rdcss_cell_attached(int dsList, struct rdcss_descriptor *d, void **a, void *v) =
    [_]ghost_list_member_handle(dsList, d) &*&
    [1/2]rdcss_descriptor_detached(d, false) &*&
    [_]descr(d, _, _, a, ?o2, ?n2, _, _) &*&
    [1/2]rdcss_descriptor_success(d, ?success) &*&
    v == (success ? n2 : o2);

predicate descr(struct rdcss_descriptor *d; void **a1, void *o1, void **a2, void *o2, void *n2, struct cas_tracker *tracker, rdcss_operation_lemma *op) =
    d->a1 |-> a1 &*& d->o1 |-> o1 &*& d->a2 |-> a2 &*& d->o2 |-> o2 &*& d->n2 |-> n2 &*& d->tracker |-> tracker &*& d->op |-> op &*& [_]is_cas_tracker(tracker);

predicate done_copy(struct rdcss_descriptor *d, bool done) = true;
predicate detached_copy(struct rdcss_descriptor *d, bool detached) = true;

predicate_ctor rdcss_descriptor(int asList, int bsList, rdcss_unseparate_lemma *unsep, any info)(struct rdcss_descriptor *d) =
    true == (((uintptr_t)d & 1) == 0) &*&
    [_]descr(d, ?a1, ?o1, ?a2, ?o2, ?n2, ?tracker, ?op) &*& [_]is_cas_tracker(tracker) &*&
    true == (((uintptr_t)o2 & 1) == 0) &*&
    true == (((uintptr_t)n2 & 1) == 0) &*&
    done_copy(d, ?done) &*&
    (done ? [_]d->done |-> true : d->done |-> false) &*&
    [?fSuccess]d->success |-> ?success &*&
    detached_copy(d, ?detached) &*&
    (detached ? [_]d->detached |-> true : [1/2]d->detached |-> false) &*&
    [1/2]d->disposed |-> ?disposed &*&
    [_]ghost_list_member_handle(asList, a1) &*&
    [_]ghost_assoc_list_member_handle(bsList, a2) &*&
    (
        detached ?
            done
        :
            cas_tracker(tracker, 0) &*&
            !disposed &*& [1/2]pointer(a2, (void *)((uintptr_t)d | 1))
    ) &*&
    done ?
        [_]tracked_cas_prediction(tracker, 0, success ? n2 : o2) &*&
        disposed ?
            true
        :
            is_rdcss_operation_lemma(op) &*& rdcss_operation_post(op)(o2)
    :
        fSuccess == 1/2 &*&
        !success &*& is_rdcss_operation_lemma(op) &*& rdcss_operation_pre(op)(unsep, info, a1, o1, a2, o2, n2);

predicate rdcss(int id, rdcss_unseparate_lemma *unsep, any info, list<void *> aas, list<pair<void *, void *> > bs) =
    [_]ghost_cell3(id, ?asList, ?bsList, ?dsList) &*&
    ghost_list(asList, aas) &*&
    ghost_assoc_list(bsList, bs) &*&
    ghost_list<void *>(dsList, ?ds) &*&
    foreach_assoc(bs, rdcss_cell(dsList)) &*& foreach(ds, rdcss_descriptor(asList, bsList, unsep, info));

@*/

/*@

lemma int create_rdcss(rdcss_unseparate_lemma *unsep, any info)
    requires true;
    ensures rdcss(result, unsep, info, nil, nil);
{
    int asList = create_ghost_list();
    int bsList = create_ghost_assoc_list();
    int dsList = create_ghost_list();
    int id = create_ghost_cell3(asList, bsList, dsList);
    close foreach_assoc(nil, rdcss_cell(dsList));
    close foreach(nil, rdcss_descriptor(asList, bsList, unsep, info));
    leak ghost_cell3(id, asList, bsList, dsList);
    close rdcss(id, unsep, info, nil, nil);
    return id;
}

lemma void rdcss_add_a(void *aa)
    requires rdcss(?id, ?unsep, ?info, ?aas, ?bs);
    ensures rdcss(id, unsep, info, cons(aa, aas), bs);
{
    open rdcss(id, unsep, info, aas, bs);
    assert [_]ghost_cell3(id, ?asList, ?bsList, ?dsList);
    ghost_list_add(asList, aa);
    close rdcss(id, unsep, info, cons(aa, aas), bs);
}

lemma void rdcss_add_b(void *ba)
    requires rdcss(?id, ?unsep, ?info, ?aas, ?bs) &*& pointer(ba, ?bv) &*& true == (((uintptr_t)bv & 1) == 0) &*& !mem_assoc(ba, bs);
    ensures rdcss(id, unsep, info, aas, cons(pair(ba, bv), bs));
{
    open rdcss(id, unsep, info, aas, bs);
    assert [_]ghost_cell3(id, ?asList, ?bsList, ?dsList);
    ghost_assoc_list_add(bsList, ba, bv);
    close rdcss_cell_frac(ba, 1);
    close rdcss_cell(dsList)(ba, bv);
    close foreach_assoc(cons(pair(ba, bv), bs), rdcss_cell(dsList));
    close rdcss(id, unsep, info, aas, cons(pair(ba, bv), bs));
}

@*/

//@ predicate prediction(void *value) = true;

void rdcss_complete(struct rdcss_descriptor *d)
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        [_]ghost_cell3(?id, ?asList, ?bsList, ?dsList) &*&
        [_]ghost_list_member_handle(dsList, d) &*&
        [_]descr(d, ?a1, ?o1, ?a2, ?o2, ?n2, ?tracker, ?op) &*&
        is_rdcss_separate_lemma(?sep) &*& is_rdcss_unseparate_lemma(?unsep) &*& rdcss_separate_lemma(sep)(?info, id, inv, unsep);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        [_]ghost_cell3(id, asList, bsList, dsList) &*&
        [_]ghost_list_member_handle(dsList, d) &*&
        [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
        [_]d->detached |-> true;
    @*/
{
    prophecy_id a1ProphecyId = create_prophecy_pointer();
    //@ assert prophecy_pointer(a1ProphecyId, ?a1Prophecy);
    prophecy_id a2ProphecyId = create_prophecy_pointer();
    //@ assert prophecy_pointer(a2ProphecyId, ?a2Prophecy);
    void *r = 0;
    {
        /*@
        predicate_family_instance atomic_load_pointer_context_pre(context1)(predicate() inv_, void **pp, void *prophecy) =
            inv_ == inv &*& pp == a1 &*& prophecy == a1Prophecy &*&
            [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
            [_]ghost_cell3(id, asList, bsList, dsList) &*&
            [_]ghost_list_member_handle(dsList, d) &*&
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep);
        predicate_family_instance atomic_load_pointer_context_post(context1)() =
            [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
            [_]ghost_cell3(id, asList, bsList, dsList) &*&
            [_]ghost_list_member_handle(dsList, d) &*&
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
            a2Prophecy == (void *)((uintptr_t)d | 1) ?
                prediction(?v) &*& [_]tracked_cas_prediction(tracker, 0, v) &*&
                v == (a1Prophecy == o1 ? n2 : o2) ?
                    [_]d->done |-> true
                :
                    true
            :
                true;
        lemma void context1(atomic_load_pointer_operation *aop) : atomic_load_pointer_context
            requires
                atomic_load_pointer_context_pre(context1)(?inv_, ?pp, ?prophecy) &*& inv_() &*&
                is_atomic_load_pointer_operation(aop) &*& atomic_load_pointer_operation_pre(aop)(pp, prophecy);
            ensures
                atomic_load_pointer_context_post(context1)() &*& inv_() &*&
                is_atomic_load_pointer_operation(aop) &*& atomic_load_pointer_operation_post(aop)();
        {
            open atomic_load_pointer_context_pre(context1)(_, _, _);
            sep();
            assert rdcss_unseparate_lemma(unsep)(info, id, inv, sep, ?aas, ?avs, ?bs);
            open rdcss(id, unsep, info, aas, bs);
            assert ghost_list(dsList, ?ds);
            ghost_list_member_handle_lemma(dsList);
            foreach_separate(ds, d);
            open rdcss_descriptor(asList, bsList, unsep, info)(d);
            ghost_list_member_handle_lemma(asList);
            mem_zip_mem_assoc_lemma(a1, aas, avs);
            foreach_assoc_separate(zip(aas, avs), a1);
            aop();
            foreach_assoc_unseparate_nochange(zip(aas, avs), a1);
            if (a2Prophecy == (void *)((uintptr_t)d | 1)) {
                void *predictedValue = create_tracked_cas_prediction(tracker, 0);
                close prediction(predictedValue);
                if (predictedValue == (a1Prophecy == o1 ? n2 : o2)) {
                    assert [_]d->done |-> ?done;
                    if (!done) {
                        op();
                        d->done = true;
                        leak d->done |-> true;
                        open done_copy(d, false);
                        close done_copy(d, true);
                        ghost_assoc_list_member_handle_lemma(bsList, a2);
                        foreach_assoc_separate(bs, a2);
                        bitand_bitor_lemma((uintptr_t)d, 1);
                        open rdcss_cell(dsList)(a2, _);
                        open rdcss_cell_attached(dsList, d, _, _);
                        if (a1Prophecy == o1) {
                            d->success = true;
                            ghost_assoc_list_update(bsList, a2, n2);
                            close rdcss_cell_attached(dsList, d, a2, n2);
                            close rdcss_cell(dsList)(a2, n2);
                            foreach_assoc_unseparate(bs, a2);
                        } else {
                            close rdcss_cell_attached(dsList, d, a2, o2);
                            close rdcss_cell(dsList)(a2, o2);
                            foreach_assoc_unseparate_nochange(bs, a2);
                        }
                    }
                }
            }
            close rdcss_descriptor(asList, bsList, unsep, info)(d);
            foreach_unseparate(ds, d);
            assert ghost_assoc_list(bsList, ?bs1);
            close rdcss(id, unsep, info, aas, bs1);
            unsep();
            close atomic_load_pointer_context_post(context1)();
        }
        @*/
        //@ close atomic_load_pointer_context_pre(context1)(inv, a1, a1Prophecy);
        //@ produce_lemma_function_pointer_chunk(context1);
        //@ open descr(d, _, _, _, _, _, _, _);
        r = atomic_load_pointer(a1ProphecyId, d->a1);
        //@ leak is_atomic_load_pointer_context(context1);
        //@ open atomic_load_pointer_context_post(context1)();
    }
    
    void *v = r == d->o1 ? d->n2 : d->o2;
    {
        /*@
        predicate_family_instance tracked_cas_ctxt_pre(context2)(struct cas_tracker *tracker_, predicate() inv_, void **pp, void *old, void *new, void *prophecy) =
            tracker_ == tracker &*& inv_ == inv &*& pp == a2 &*& old == (void *)((uintptr_t)d | 1) &*& new == v &*& prophecy == a2Prophecy &*&
            [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
            [_]ghost_cell3(id, asList, bsList, dsList) &*&
            [_]ghost_list_member_handle(dsList, d) &*&
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
            a2Prophecy == (void *)((uintptr_t)d | 1) ?
                prediction(?w) &*& [_]tracked_cas_prediction(tracker, 0, w) &*&
                w == (a1Prophecy == o1 ? n2 : o2) ?
                    [_]d->done |-> true
                :
                    true
            :
                true;
        predicate_family_instance tracked_cas_ctxt_post(context2)() =
            [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
            [_]ghost_cell3(id, asList, bsList, dsList) &*&
            [_]ghost_list_member_handle(dsList, d) &*&
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
            [_]d->detached |-> true;
        lemma void context2(tracked_cas_operation *aop) : tracked_cas_ctxt
            requires
                tracked_cas_ctxt_pre(context2)(?tracker_, ?inv_, ?pp, ?old, ?new, ?prophecy) &*& inv_() &*&
                is_tracked_cas_operation(aop) &*& tracked_cas_pre(aop)(tracker_, pp, old, new, prophecy);
            ensures
                tracked_cas_ctxt_post(context2)() &*& inv_() &*&
                is_tracked_cas_operation(aop) &*& tracked_cas_post(aop)();
        {
            open tracked_cas_ctxt_pre(context2)(_, _, _, _, _, _);
            sep();
            open rdcss(id, unsep, info, ?as, ?bs);
            ghost_list_member_handle_lemma(dsList);
            assert ghost_list(dsList, ?ds);
            foreach_separate(ds, d);
            open rdcss_descriptor(asList, bsList, unsep, info)(d);
            ghost_assoc_list_member_handle_lemma(bsList, a2);
            foreach_assoc_separate(bs, a2);
            bitand_bitor_lemma((uintptr_t)d, 1);
            open rdcss_cell(dsList)(a2, ?abstractValue);
            assert [_]pointer(a2, ?w);
            if (w == (void *)((uintptr_t)d | 1)) {
                open rdcss_cell_attached(dsList, d, a2, abstractValue);
                if (a2Prophecy == w) {
                    open prediction(?w0);
                    if (w0 == (a1Prophecy == o1 ? n2 : o2)) {
                        aop(0, w0);
                        d->detached = true;
                        leak d->detached |-> true;
                        open detached_copy(d, false);
                        close detached_copy(d, true);
                        open rdcss_cell_frac(a2, 1/2);
                        close rdcss_cell_frac(a2, 1);
                        assert [_]d->success |-> ?success;
                        w = success ? n2 : o2;
                        leak cas_tracker(tracker, 1);
                    } else {
                        aop(0, w0);
                    }
                } else {
                    void *dummyPrediction = create_tracked_cas_prediction(tracker, 0);
                    aop(0, dummyPrediction);
                }
            } else {
                aop(0, 0);
            }
            close rdcss_cell(dsList)(a2, abstractValue);
            foreach_assoc_unseparate_nochange(bs, a2);
            close rdcss_descriptor(asList, bsList, unsep, info)(d);
            foreach_unseparate(ds, d);
            close rdcss(id, unsep, info, as, bs);
            unsep();
            close tracked_cas_ctxt_post(context2)();
        }
        @*/
        //@ close tracked_cas_ctxt_pre(context2)(tracker, inv, a2, (void *)((uintptr_t)d | 1), v, a2Prophecy);
        //@ produce_lemma_function_pointer_chunk(context2);
        tracked_cas(a2ProphecyId, d->tracker, d->a2, (void *)((uintptr_t)d | 1), v);
        //@ leak is_tracked_cas_ctxt(context2);
        //@ open tracked_cas_ctxt_post(context2)();
    }
}

void *rdcss(void **a1, void *o1, void **a2, void *o2, void *n2)
    /*@
    requires
        true == (((uintptr_t)o2 & 1) == 0) &*&
        true == (((uintptr_t)n2 & 1) == 0) &*&
        [?f]atomic_space(?inv) &*&
        is_rdcss_separate_lemma(?sep) &*& is_rdcss_unseparate_lemma(?unsep) &*& rdcss_separate_lemma(sep)(?info, ?id, inv, unsep) &*&
        is_rdcss_as_membership_lemma(?asMem) &*& rdcss_as_membership_lemma(asMem)(unsep, info, a1) &*&
        is_rdcss_bs_membership_lemma(?bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
        is_rdcss_operation_lemma(?op) &*& rdcss_operation_pre(op)(unsep, info, a1, o1, a2, o2, n2);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
        is_rdcss_as_membership_lemma(asMem) &*& rdcss_as_membership_lemma(asMem)(unsep, info, a1) &*&
        is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
        is_rdcss_operation_lemma(op) &*& rdcss_operation_post(op)(result);
    @*/
{
    struct cas_tracker *tracker = create_cas_tracker();
    struct rdcss_descriptor *d = malloc(sizeof(struct rdcss_descriptor));
    if (d == 0) abort();
    if (((uintptr_t)d & 1) != 0) abort();
    d->a1 = a1;
    d->o1 = o1;
    d->a2 = a2;
    d->o2 = o2;
    d->n2 = n2;
    d->tracker = tracker;
    //@ d->op = op;
    //@ d->done = false;
    //@ d->success = false;
    //@ d->detached = false;
    //@ d->disposed = false;
    //@ close descr(d, a1, o1, a2, o2, n2, tracker, op);
    //@ leak descr(d, a1, o1, a2, o2, n2, tracker, op);
loop:
    /*@
    invariant
        true == (((uintptr_t)d & 1) == 0) &*&
        [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*& d->done |-> false &*& d->success |-> false &*& d->detached |-> false &*& d->disposed |-> false &*&
        cas_tracker(tracker, 0) &*& [_]is_cas_tracker(tracker) &*&
        malloc_block_rdcss_descriptor(d) &*&
        [f]atomic_space(inv) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
        is_rdcss_as_membership_lemma(asMem) &*& rdcss_as_membership_lemma(asMem)(unsep, info, a1) &*&
        is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
        is_rdcss_operation_lemma(op) &*& rdcss_operation_pre(op)(unsep, info, a1, o1, a2, o2, n2);
    @*/
    prophecy_id prophecyId = create_prophecy_pointer();
    //@ assert prophecy_pointer(prophecyId, ?prophecy);
    void *r = 0;
    {
        /*@
        predicate_family_instance atomic_compare_and_store_pointer_context_pre(context)(predicate() inv_, void **p, void *old, void *new, void *prophecy_) =
            inv_ == inv &*& p == a2 &*& old == o2 &*& new == (void *)((uintptr_t)d | 1) &*& prophecy_ == prophecy &*&
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
            is_rdcss_as_membership_lemma(asMem) &*& rdcss_as_membership_lemma(asMem)(unsep, info, a1) &*&
            is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
            is_rdcss_operation_lemma(op) &*& rdcss_operation_pre(op)(unsep, info, a1, o1, a2, o2, n2) &*&
            [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*& [_]is_cas_tracker(tracker) &*&
            cas_tracker(tracker, 0) &*&
            d->done |-> false &*& d->success |-> false &*& d->detached |-> false &*& d->disposed |-> false;
        
        predicate_family_instance atomic_compare_and_store_pointer_context_post(context)() =
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
            is_rdcss_as_membership_lemma(asMem) &*& rdcss_as_membership_lemma(asMem)(unsep, info, a1) &*&
            is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
            prophecy == o2 ?
                [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
                [_]ghost_cell3(id, ?asList, ?bsList, ?dsList) &*&
                [_]ghost_list_member_handle(dsList, d) &*& [1/2]d->disposed |-> false
            :
                true == (((uintptr_t)prophecy & 1) == 0) ?
                    is_rdcss_operation_lemma(op) &*& rdcss_operation_post(op)(prophecy)
                :
                    [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
                    [_]ghost_cell3(id, ?asList, ?bsList, ?dsList) &*&
                    d->done |-> false &*& d->success |-> false &*& d->detached |-> false &*& d->disposed |-> false &*&
                    cas_tracker(tracker, 0) &*&
                    is_rdcss_operation_lemma(op) &*& rdcss_operation_pre(op)(unsep, info, a1, o1, a2, o2, n2) &*&
                    [_]ghost_list_member_handle(dsList, (void *)((uintptr_t)prophecy & ~1)) &*&
                    [_]descr((void *)((uintptr_t)prophecy & ~1), _, _, _, _, _, _, _);
        
        lemma void context(atomic_compare_and_store_pointer_operation *aop) : atomic_compare_and_store_pointer_context
            requires
                atomic_compare_and_store_pointer_context_pre(context)(?inv_, ?pp, ?old, ?new, ?prophecy_) &*&
                is_atomic_compare_and_store_pointer_operation(aop) &*& atomic_compare_and_store_pointer_operation_pre(aop)(pp, old, new, prophecy_) &*&
                inv_();
            ensures
                atomic_compare_and_store_pointer_context_post(context)() &*&
                is_atomic_compare_and_store_pointer_operation(aop) &*& atomic_compare_and_store_pointer_operation_post(aop)() &*&
                inv_();
        {
            open atomic_compare_and_store_pointer_context_pre(context)(_, _, _, _, _);
            sep();
            asMem();
            bsMem();
            open rdcss(_, _, _, ?as, ?bs);
            assert [_]ghost_cell3(id, ?asList, ?bsList, ?dsList);
            assert ghost_list(dsList, ?ds);
            foreach_assoc_separate(bs, a2);
            open rdcss_cell(dsList)(a2, ?abstractValue);
            aop();
            if (prophecy == o2) {
                // We install the descriptor.
                ghost_list_add(dsList, d);
                bitand_bitor_lemma((uintptr_t)d, 1);
                open rdcss_cell_frac(a2, 1);
                close rdcss_cell_frac(a2, 1/2);
                close rdcss_cell_attached(dsList, d, a2, o2);
                close rdcss_cell(dsList)(a2, o2);
                foreach_assoc_unseparate_nochange(bs, a2);
                ghost_list_create_member_handle(asList, a1);
                ghost_assoc_list_create_member_handle(bsList, a2);
                close done_copy(d, false);
                close detached_copy(d, false);
                close rdcss_descriptor(asList, bsList, unsep, info)(d);
                close foreach(cons((void *)d, ds), rdcss_descriptor(asList, bsList, unsep, info));
                close rdcss(id, unsep, info, as, bs);
            } else if (((uintptr_t)prophecy & 1) == 0) {
                // Failure.
                close rdcss_cell(dsList)(a2, prophecy);
                foreach_assoc_unseparate_nochange(bs, a2);
                close rdcss(id, unsep, info, as, bs);
                op();
                leak d->disposed |-> false;
                leak d->detached |-> false;
                leak d->success |-> false;
                leak d->done |-> false;
                leak cas_tracker(tracker, 0);
            } else {
                // We bumped into another descriptor. Extract a chunk saying that it's in the atomic space.
                open rdcss_cell_attached(dsList, ?d0, ?a20, ?abstractValue0);
                close rdcss_cell_attached(dsList, d0, a20, abstractValue0);
                close rdcss_cell(dsList)(a2, abstractValue);
                foreach_assoc_unseparate_nochange(bs, a2);
                close rdcss(id, unsep, info, as, bs);
            }
            unsep();
            close atomic_compare_and_store_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_compare_and_store_pointer_context_pre(context)(inv, a2, o2, (void *)((uintptr_t)d | 1), prophecy);
        //@ produce_lemma_function_pointer_chunk(context);
        //@ produce_limits(d);
        r = atomic_compare_and_store_pointer(prophecyId, a2, o2, (void *)((uintptr_t)d | 1));
        //@ leak is_atomic_compare_and_store_pointer_context(context);
        //@ open atomic_compare_and_store_pointer_context_post(context)();
    }
    if (((uintptr_t)r & 1) != 0) {
        rdcss_complete((void *)((uintptr_t)r & ~(unsigned)1));
        //@ leak [_]rdcss_descriptor_detached((void *)((uintptr_t)r & ~1), _);
        //@ leak [_]descr((void *)((uintptr_t)r & ~1), _, _, _, _, _, _, _);
        //@ leak [_]ghost_cell3(id, ?asList, ?bsList, ?dsList);
        //@ leak [_]ghost_list_member_handle(dsList, (void *)((uintptr_t)r & ~1));
        goto loop;
    }
    if (r == o2) {
        rdcss_complete(d);
        {
            /*@
            predicate_family_instance atomic_noop_context_pre(context)(predicate() inv_) =
                inv_ == inv &*&
                is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
                [_]ghost_cell3(id, ?asList, ?bsList, ?dsList) &*&
                [_]ghost_list_member_handle(dsList, d) &*&
                [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
                [1/2]d->disposed |-> false &*&
                [_]d->detached |-> true;
            predicate_family_instance atomic_noop_context_post(context)() =
                is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
                is_rdcss_operation_lemma(op) &*& rdcss_operation_post(op)(r);
            lemma void context() : atomic_noop_context
                requires atomic_noop_context_pre(context)(?inv_) &*& inv_();
                ensures atomic_noop_context_post(context)() &*& inv_();
            {
                open atomic_noop_context_pre(context)(_);
                sep();
                open rdcss(id, unsep, info, ?as, ?bs);
                assert [_]ghost_cell3(id, ?asList, ?bsList, ?dsList);
                ghost_list_member_handle_lemma(dsList);
                assert ghost_list(dsList, ?ds);
                foreach_separate(ds, d);
                open rdcss_descriptor(asList, bsList, unsep, info)(d);
                d->disposed = true;
                split_fraction rdcss_descriptor_disposed(d, _);
                close rdcss_descriptor(asList, bsList, unsep, info)(d);
                foreach_unseparate(ds, d);
                close rdcss(id, unsep, info, as, bs);
                unsep();
                close atomic_noop_context_post(context)();
                leak [_]d->disposed |-> _;
                leak [_]ghost_list_member_handle(dsList, d);
            }
            @*/
            //@ close atomic_noop_context_pre(context)(inv);
            //@ produce_lemma_function_pointer_chunk(context);
            //@ atomic_noop();
            //@ leak is_atomic_noop_context(context);
            //@ open atomic_noop_context_post(context)();
        }
    }
    
    // We do not explicitly free the descriptor records. We assume a garbage collector (e.g. Boehm-Weiser).
    // Notice that the bitwise operations on the pointers do not hamper GC since whenever a masked version of a pointer is reachable,
    // an unmasked version of that pointer is also reachable.
    //@ leak malloc_block_rdcss_descriptor(d);
    return r;
}

void *rdcss_read(void **a2)
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_rdcss_separate_lemma(?sep) &*& is_rdcss_unseparate_lemma(?unsep) &*& rdcss_separate_lemma(sep)(?info, ?id, inv, unsep) &*&
        is_rdcss_bs_membership_lemma(?bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
        is_rdcss_read_operation_lemma(?op) &*& rdcss_read_operation_pre(op)(unsep, info, a2);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
        is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
        is_rdcss_read_operation_lemma(op) &*& rdcss_read_operation_post(op)(result);
    @*/
{
loop:
    /*@
    invariant
        [f]atomic_space(inv) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
        is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
        is_rdcss_read_operation_lemma(op) &*& rdcss_read_operation_pre(op)(unsep, info, a2);
    @*/
    void *r = 0;
    prophecy_id prophecyId = create_prophecy_pointer();
    //@ assert prophecy_pointer(prophecyId, ?prophecy);
    {
        /*@
        predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv_, void **pp, void *prophecy_) =
            inv_ == inv &*& pp == a2 &*& prophecy_ == prophecy &*&
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
            is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
            is_rdcss_read_operation_lemma(op) &*& rdcss_read_operation_pre(op)(unsep, info, a2);
        predicate_family_instance atomic_load_pointer_context_post(context)() =
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
            is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
            is_rdcss_read_operation_lemma(op) &*&
            true == (((uintptr_t)prophecy & 1) == 0) ?
                rdcss_read_operation_post(op)(prophecy)
            :
                rdcss_read_operation_pre(op)(unsep, info, a2) &*&
                [_]ghost_cell3(id, ?asList, ?bsList, ?dsList) &*&
                [_]ghost_list_member_handle(dsList, (void *)((uintptr_t)prophecy & ~1)) &*&
                [_]descr((void *)((uintptr_t)prophecy & ~1), _, _, _, _, _, _, _);
        lemma void context(atomic_load_pointer_operation *aop) : atomic_load_pointer_context
            requires
                atomic_load_pointer_context_pre(context)(?inv_, ?pp, ?prophecy_) &*& inv_() &*&
                is_atomic_load_pointer_operation(aop) &*& atomic_load_pointer_operation_pre(aop)(pp, prophecy_);
            ensures
                atomic_load_pointer_context_post(context)() &*& inv_() &*&
                is_atomic_load_pointer_operation(aop) &*& atomic_load_pointer_operation_post(aop)();
        {
            open atomic_load_pointer_context_pre(context)(_, _, _);
            sep();
            bsMem();
            open rdcss(id, unsep, info, ?as, ?bs);
            assert [_]ghost_cell3(id, ?asList, ?bsList, ?dsList);
            assert ghost_list(dsList, ?ds);
            foreach_assoc_separate(bs, a2);
            open rdcss_cell(dsList)(a2, ?abstractValue);
            aop();
            if (((uintptr_t)prophecy & 1) == 0) {
                op();
            } else {
                open rdcss_cell_attached(dsList, ?d, a2, abstractValue);
                close rdcss_cell_attached(dsList, d, a2, abstractValue);
            }
            close rdcss_cell(dsList)(a2, abstractValue);
            foreach_assoc_unseparate_nochange(bs, a2);
            close rdcss(id, unsep, info, as, bs);
            unsep();
            close atomic_load_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_load_pointer_context_pre(context)(inv, a2, prophecy);
        //@ produce_lemma_function_pointer_chunk(context);
        r = atomic_load_pointer(prophecyId, a2);
        //@ leak is_atomic_load_pointer_context(context);
        //@ open atomic_load_pointer_context_post(context)();
    }
    if (((uintptr_t)r & 1) != 0) {
        rdcss_complete((void *)((uintptr_t)r & ~(unsigned)1));
        //@ leak [_]rdcss_descriptor_detached(_, _);
        //@ leak [_]ghost_cell3(_, _, _, _);
        //@ leak [_]ghost_list_member_handle(_, _);
        //@ leak [_]descr(_, _, _ ,_, _, _, _, _);
        goto loop;
    }
    return r;
}

bool rdcss_compare_and_store(void **a2, void *o2, void *n2)
    /*@
    requires
        true == (((uintptr_t)o2 & 1) == 0) &*&
        true == (((uintptr_t)n2 & 1) == 0) &*&
        [?f]atomic_space(?inv) &*&
        is_rdcss_separate_lemma(?sep) &*& is_rdcss_unseparate_lemma(?unsep) &*& rdcss_separate_lemma(sep)(?info, ?id, inv, unsep) &*&
        is_rdcss_bs_membership_lemma(?bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
        is_rdcss_cas_lemma(?op) &*& rdcss_cas_pre(op)(unsep, info, a2, o2, n2);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
        is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
        is_rdcss_cas_lemma(op) &*& rdcss_cas_post(op)(result);
    @*/
{
    prophecy_id casProphecyId = create_prophecy_pointer();
    //@ assert prophecy_pointer(casProphecyId, ?casProphecy);
    void *r = 0;
    {
        /*@
        predicate_family_instance atomic_compare_and_store_pointer_context_pre(context)(predicate() inv_, void **pp, void *old, void *new, void *prophecy) =
            inv_ == inv &*& pp == a2 &*& old == o2 &*& new == n2 &*& prophecy == casProphecy &*&
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
            is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
            is_rdcss_cas_lemma(op) &*& rdcss_cas_pre(op)(unsep, info, a2, o2, n2);
        predicate_family_instance atomic_compare_and_store_pointer_context_post(context)() =
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(info, id, inv, unsep) &*&
            is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, info, a2) &*&
            is_rdcss_cas_lemma(op) &*& rdcss_cas_post(op)(casProphecy == o2);
        lemma void context(atomic_compare_and_store_pointer_operation *aop) : atomic_compare_and_store_pointer_context
            requires
                atomic_compare_and_store_pointer_context_pre(context)(?inv_, ?pp, ?old, ?new, ?prophecy) &*& inv_() &*&
                is_atomic_compare_and_store_pointer_operation(aop) &*& atomic_compare_and_store_pointer_operation_pre(aop)(pp, old, new, prophecy);
            ensures
                atomic_compare_and_store_pointer_context_post(context)() &*& inv_() &*&
                is_atomic_compare_and_store_pointer_operation(aop) &*& atomic_compare_and_store_pointer_operation_post(aop)();
        {
            open atomic_compare_and_store_pointer_context_pre(context)(_, _, _, _, _);
            sep();
            bsMem();
            open rdcss(id, unsep, info, ?aas, ?bs);
            assert [_]ghost_cell3(id, _, ?bsList, ?dsList);
            foreach_assoc_separate(bs, a2);
            open rdcss_cell(dsList)(a2, ?oldValue);
            aop();
            if (casProphecy == o2) {
                close rdcss_cell(dsList)(a2, n2);
                foreach_assoc_unseparate(bs, a2);
                ghost_assoc_list_update(bsList, a2, n2);
                close rdcss(id, unsep, info, aas, update_assoc(bs, a2, n2));
            } else {
                close rdcss_cell(dsList)(a2, oldValue);
                foreach_assoc_unseparate_nochange(bs, a2);
                close rdcss(id, unsep, info, aas, bs);
            }
            op(casProphecy == o2);
            unsep();
            close atomic_compare_and_store_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_compare_and_store_pointer_context_pre(context)(inv, a2, o2, n2, casProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        r = atomic_compare_and_store_pointer(casProphecyId, a2, o2, n2);
        //@ leak is_atomic_compare_and_store_pointer_context(context);
        //@ open atomic_compare_and_store_pointer_context_post(context)();
    }
    return r == o2;
}
