#include "stdlib.h"
#include "atomics.h"
#include "list.h"

// A port of the RDCSS [1] proof by Vafeiadis [2] to VeriFast
// [1] Tim Harris, Keir Fraser, and Ian A. Pratt. A practical multi-word compare-and-swap operation.
//     In 16th International Symposium on Distributed Computing, pages 265-279, October 2002.
// [2] Viktor Vafeiadis. Modular verification of fine-grained concurrency. PhD Thesis. Computer Laboratory, University of Cambridge. July 2008.

// As in [2], this version of the algorithm does not perform descriptor cleanup; i.e., a garbage collector is assumed.

/*@

lemma void bitand_bitor_lemma(uintptr_t x, uintptr_t y);
    requires true == ((x & y) == 0);
    ensures y == ((x | y) & y) &*& x == ((x | y) & ~y);

inductive pair<a, b> = pair(a, b);

predicate ghost_cell3(int id; int v1, int v2, int v3);

fixpoint bool mem_assoc(void **x, list<pair<void *, void *> > xys) {
    switch (xys) {
        case nil: return false;
        case cons(xy, xys0): return
            switch (xy) {
                case pair(x0, y0): return x0 == x || mem_assoc(x, xys0);
            };
    }
}

fixpoint void *assoc(void **x, list<pair<void *, void *> > xys) {
    switch (xys) {
        case nil: return 0;
        case cons(xy, xys0): return
            switch (xy) {
                case pair(x0, y0): return x0 == x ? y0 : assoc(x, xys0);
            };
    }
}

fixpoint list<pair<void *, void *> > update(list<pair<void *, void *> > xys, void **x, void *y) {
    switch (xys) {
        case nil: return nil;
        case cons(xy, xys0): return
            switch (xy) {
                case pair(x0, y0): return x0 == x ? cons(pair(x0, y), xys0) : cons(pair(x0, y0), update(xys0, x, y));
            };
    }
}

fixpoint list<pair<void *, void *> > before_assoc(void **x, list<pair<void *, void *> > xys) {
    switch (xys) {
        case nil: return nil;
        case cons(xy, xys0): return
            switch (xy) {
                case pair(x0, y0): return x0 == x ? nil : cons(pair(x0, y0), before_assoc(x, xys0));
            };
    }
}

fixpoint list<pair<void *, void *> > after_assoc(void **x, list<pair<void *, void *> > xys) {
    switch (xys) {
        case nil: return nil;
        case cons(xy, xys0): return
            switch (xy) {
                case pair(x0, y0): return x0 == x ? xys0 : after_assoc(x, xys0);
            };
    }
}

lemma int create_ghost_cell3(int v1, int v2, int v3);
    requires true;
    ensures ghost_cell3(result, v1, v2, v3);

predicate ghost_list(int id, list<void *> xs);
predicate ghost_list_member_handle(int id, void *d);

lemma int create_ghost_list();
    requires true;
    ensures ghost_list(result, nil);

lemma void ghost_list_add(int id, void *d);
    requires ghost_list(id, ?ds);
    ensures ghost_list(id, cons(d, ds)) &*& ghost_list_member_handle(id, d);

lemma void ghost_list_member_handle_lemma();
    requires [?f1]ghost_list(?id, ?ds) &*& [?f2]ghost_list_member_handle(id, ?d);
    ensures [f1]ghost_list(id, ds) &*& [f2]ghost_list_member_handle(id, d) &*& mem(d, ds) == true;

lemma void ghost_list_create_member_handle(int id, void *x);
    requires [?f1]ghost_list(id, ?xs) &*& mem(x, xs) == true;
    ensures [f1]ghost_list(id, xs) &*& [_]ghost_list_member_handle(id, x);

predicate ghost_assoc_list(int id, list<pair<void *, void *> > xs);
predicate ghost_assoc_list_member_handle(int id, void **pp);

lemma int create_ghost_assoc_list();
    requires true;
    ensures ghost_assoc_list(result, nil);

lemma void ghost_assoc_list_update(int id, void **x, void *y);
    requires ghost_assoc_list(id, ?xys) &*& mem_assoc(x, xys) == true;
    ensures ghost_assoc_list(id, update(xys, x, y));

lemma void ghost_assoc_list_create_member_handle(int id, void **x);
    requires [?f1]ghost_assoc_list(id, ?xys) &*& mem_assoc(x, xys) == true;
    ensures [f1]ghost_assoc_list(id, xys) &*& [_]ghost_assoc_list_member_handle(id, x);

lemma void ghost_assoc_list_member_handle_lemma(int id, void **x);
    requires [?f1]ghost_assoc_list(id, ?xys) &*& [?f2]ghost_assoc_list_member_handle(id, x);
    ensures [f1]ghost_assoc_list(id, xys) &*& [f2]ghost_assoc_list_member_handle(id, x) &*& mem_assoc(x, xys) == true;

predicate foreach(list<void *> xs, predicate(void *) p) =
    switch (xs) {
        case nil: return true;
        case cons(x, xs0): return p(x) &*& foreach(xs0, p);
    };

lemma void foreach_separate(list<void *> xs, void *x);
    requires foreach(xs, ?p) &*& mem(x, xs) == true;
    ensures foreach(before(x, xs), p) &*& p(x) &*& foreach(after(x, xs), p);

lemma void foreach_unseparate(list<void *> xs, void *x);
    requires mem(x, xs) == true &*& foreach(before(x, xs), ?p) &*& p(x) &*& foreach(after(x, xs), p);
    ensures foreach(xs, p);

predicate foreach_assoc(list<pair<void *, void *> > xys, predicate(void **, void *) p) =
    switch (xys) {
        case nil: return true;
        case cons(xy, xys0): return
            switch (xy) {
                case pair(x, y): return p(x, y) &*& foreach_assoc(xys0, p);
            };
    };

lemma void foreach_assoc_separate(list<pair<void *, void *> > xys, void **x);
    requires foreach_assoc(xys, ?p) &*& mem_assoc(x, xys) == true;
    ensures foreach_assoc(before_assoc(x, xys), p) &*& p(x, assoc(x, xys)) &*& foreach_assoc(after_assoc(x, xys), p);

lemma void foreach_assoc_unseparate(list<pair<void *, void *> > xys, void **x);
    requires mem_assoc(x, xys) == true &*& foreach_assoc(before_assoc(x, xys), ?p) &*& p(x, ?y) &*& foreach_assoc(after_assoc(x, xys), p);
    ensures foreach_assoc(update(xys, x, y), p);

lemma void foreach_assoc_unseparate_nochange(list<pair<void *, void *> > xys, void **x);
    requires mem_assoc(x, xys) == true &*& foreach_assoc(before_assoc(x, xys), ?p) &*& p(x, assoc(x, xys)) &*& foreach_assoc(after_assoc(x, xys), p);
    ensures foreach_assoc(xys, p);

fixpoint list<pair<void *, void *> > zip(list<void *> xs, list<void *> ys) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return
            switch (ys) {
                case nil: return cons(pair(x, x), zip(xs0, nil));
                case cons(y, ys0): return cons(pair(x, y), zip(xs0, ys0));
            };
    }
}

lemma void mem_zip_mem_assoc_lemma(void *x, list<void *> xs, list<void *> ys);
    requires mem(x, xs) == true;
    ensures mem_assoc(x, zip(xs, ys)) == true;

@*/

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

predicate_ctor rdcss_cell(int dsList)(void **a, void *v) requires
    [?f]pointer(a, ?w) &*&
    true == (((uintptr_t)w & 1) == 0) ?
        f == 1 &*& w == v
    :
        f == 1/2 &*&
        [_]ghost_list_member_handle(dsList, (struct rdcss_descriptor *)((uintptr_t)w & ~1)) &*&
        [1/2]rdcss_descriptor_detached((struct rdcss_descriptor *)((uintptr_t)w & ~1), false) &*&
        [_]descr((struct rdcss_descriptor *)((uintptr_t)w & ~1), _, _, a, ?o2, ?n2, _, _) &*&
        [1/2]rdcss_descriptor_success((struct rdcss_descriptor *)((uintptr_t)w & ~1), ?success) &*&
        v == (success ? n2 : o2);

predicate descr(struct rdcss_descriptor *d; void **a1, void *o1, void **a2, void *o2, void *n2, struct cas_tracker *tracker, rdcss_operation_lemma *op) =
    d->a1 |-> a1 &*& d->o1 |-> o1 &*& d->a2 |-> a2 &*& d->o2 |-> o2 &*& d->n2 |-> n2 &*& d->tracker |-> tracker &*& d->op |-> op;

predicate_ctor rdcss_descriptor(int asList, int bsList, rdcss_unseparate_lemma *unsep)(struct rdcss_descriptor *d) requires
    true == (((uintptr_t)d & 1) == 0) &*&
    [_]descr(d, ?a1, ?o1, ?a2, ?o2, ?n2, ?tracker, ?op) &*&
    true == (((uintptr_t)o2 & 1) == 0) &*&
    true == (((uintptr_t)n2 & 1) == 0) &*&
    [?f]d->done |-> ?done &*&
    [?fSuccess]d->success |-> ?success &*&
    [?fDetached]d->detached |-> ?detached &*&
    [1/2]d->disposed |-> ?disposed &*&
    [_]ghost_list_member_handle(asList, a1) &*&
    [_]ghost_assoc_list_member_handle(bsList, a2) &*&
    (
        detached ?
            done
        :
            cas_tracker(tracker, 0) &*&
            fDetached == 1/2 &*&
            !disposed &*& [1/2]pointer(a2, (void *)((uintptr_t)d | 1))
    ) &*&
    done ?
        [_]tracked_cas_prediction(tracker, 0, success ? n2 : o2) &*&
        disposed ?
            true
        :
            is_rdcss_operation_lemma(op) &*& rdcss_operation_post(op)(o2)
    :
        f == 1 &*& fSuccess == 1/2 &*&
        !success &*& is_rdcss_operation_lemma(op) &*& rdcss_operation_pre(op)(unsep, a1, o1, a2, o2, n2);

predicate rdcss(int id, rdcss_unseparate_lemma *unsep, list<void *> aas, list<pair<void *, void *> > bs) =
    [_]ghost_cell3(id, ?asList, ?bsList, ?dsList) &*&
    ghost_list(asList, aas) &*&
    ghost_assoc_list(bsList, bs) &*&
    ghost_list(dsList, ?ds) &*&
    foreach_assoc(bs, rdcss_cell(dsList)) &*& foreach(ds, rdcss_descriptor(asList, bsList, unsep));

@*/

/*@

predicate_family rdcss_separate_lemma(void *sep)(int id, predicate() inv, rdcss_unseparate_lemma *unsep);
predicate_family rdcss_unseparate_lemma(void *unsep)(int id, predicate() inv, rdcss_separate_lemma *sep, list<void *> aas, list<void *> avs, list<pair<void *, void *> > bs);

typedef lemma void rdcss_separate_lemma();
    requires rdcss_separate_lemma(this)(?id, ?inv, ?unsep) &*& inv();
    ensures rdcss_unseparate_lemma(unsep)(id, inv, this, ?aas, ?avs, ?bs) &*& foreach_assoc(zip(aas, avs), pointer) &*& rdcss(id, unsep, aas, bs);

typedef lemma void rdcss_unseparate_lemma();
    requires rdcss_unseparate_lemma(this)(?id, ?inv, ?sep, ?aas, ?avs, ?bs) &*& foreach_assoc(zip(aas, avs), pointer) &*& rdcss(id, this, aas, bs);
    ensures rdcss_separate_lemma(sep)(id, inv, this) &*& inv();

predicate_family rdcss_operation_pre(void *op)(rdcss_unseparate_lemma *unsep, void **a1, void *o1, void **a2, void *o2, void *n2);
predicate_family rdcss_operation_post(void *op)(void *result);

typedef lemma void *rdcss_operation_lemma();
    requires rdcss_operation_pre(this)(?unsep, ?a1, ?o1, ?a2, ?o2, ?n2) &*& rdcss_unseparate_lemma(unsep)(?id, ?inv, ?sep, ?aas, ?avs, ?bs);
    ensures
        rdcss_operation_post(this)(result) &*& mem((void *)a1, aas) == true &*& mem_assoc(a2, bs) == true &*& result == assoc(a2, bs) &*&
        assoc(a1, zip(aas, avs)) == o1 && assoc(a2, bs) == o2 ?
            rdcss_unseparate_lemma(unsep)(id, inv, sep, aas, avs, update(bs, a2, n2))
        :
            rdcss_unseparate_lemma(unsep)(id, inv, sep, aas, avs, bs);

predicate_family rdcss_as_membership_lemma(void *mem)(rdcss_unseparate_lemma *unsep, void **a1);

typedef lemma void rdcss_as_membership_lemma();
    requires rdcss_as_membership_lemma(this)(?unsep, ?a1) &*& rdcss_unseparate_lemma(unsep)(?id, ?inv, ?sep, ?aas, ?avs, ?bs);
    ensures rdcss_as_membership_lemma(this)(unsep, a1) &*& rdcss_unseparate_lemma(unsep)(id, inv, sep, aas, avs, bs) &*& mem((void *)a1, aas) == true;

predicate_family rdcss_bs_membership_lemma(void *mem)(rdcss_unseparate_lemma *unsep, void **a2);

typedef lemma void rdcss_bs_membership_lemma();
    requires rdcss_bs_membership_lemma(this)(?unsep, ?a2) &*& rdcss_unseparate_lemma(unsep)(?id, ?inv, ?sep, ?aas, ?avs, ?bs);
    ensures rdcss_bs_membership_lemma(this)(unsep, a2) &*& rdcss_unseparate_lemma(unsep)(id, inv, sep, aas, avs, bs) &*& mem_assoc(a2, bs) == true;

@*/

/*@

lemma int create_rdcss(rdcss_unseparate_lemma *unsep)
    requires true;
    ensures rdcss(result, unsep, nil, nil);
{
    int asList = create_ghost_list();
    int bsList = create_ghost_assoc_list();
    int dsList = create_ghost_list();
    int id = create_ghost_cell3(asList, bsList, dsList);
    close foreach_assoc(nil, rdcss_cell(dsList));
    close foreach(nil, rdcss_descriptor(asList, bsList, unsep));
    close rdcss(id, unsep, nil, nil);
    return id;
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
        is_rdcss_separate_lemma(?sep) &*& is_rdcss_unseparate_lemma(?unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        [_]ghost_cell3(id, asList, bsList, dsList) &*&
        [_]ghost_list_member_handle(dsList, d) &*&
        [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
        [_]d->detached |-> true;
    @*/
{
    //@ split_fraction descr(d, _, _, _, _, _, _, _);
    //@ open [?fDescr]descr(d, _, _, _, _, _, _, _);
    //@ void *a1Prophecy = create_prophecy_pointer();
    //@ void *a2Prophecy = create_prophecy_pointer();
    void *r = 0;
    {
        /*@
        predicate_family_instance atomic_load_pointer_context_pre(context1)(predicate() inv_, void **pp, void *prophecy) =
            inv_ == inv &*& pp == a1 &*& prophecy == a1Prophecy &*&
            [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
            [_]ghost_cell3(id, asList, bsList, dsList) &*&
            [_]ghost_list_member_handle(dsList, d) &*&
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep);
        predicate_family_instance atomic_load_pointer_context_post(context1)() =
            [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
            [_]ghost_cell3(id, asList, bsList, dsList) &*&
            [_]ghost_list_member_handle(dsList, d) &*&
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
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
            assert rdcss_unseparate_lemma(unsep)(id, inv, sep, ?aas, ?avs, ?bs);
            open rdcss(id, unsep, aas, bs);
            merge_fractions ghost_cell3(id, _, _, _);
            split_fraction ghost_cell3(id, _, _, _);
            assert ghost_list(dsList, ?ds);
            ghost_list_member_handle_lemma();
            foreach_separate(ds, d);
            open rdcss_descriptor(asList, bsList, unsep)(d);
            merge_fractions descr(d, _, _, _, _, _, _, _);
            split_fraction descr(d, _, _, _, _, _, _, _);
            ghost_list_member_handle_lemma();
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
                        ghost_assoc_list_member_handle_lemma(bsList, a2);
                        foreach_assoc_separate(bs, a2);
                        open rdcss_cell(dsList)(a2, _);
                        merge_fractions pointer(a2, _);
                        split_fraction pointer(a2, _);
                        bitand_bitor_lemma((uintptr_t)d, 1);
                        merge_fractions descr(d, _, _, _, _, _, _, _);
                        merge_fractions descr(d, _, _, _, _, _, _, _);
                        split_fraction descr(d, _, _, _, _, _, _, _);
                        split_fraction descr(d, _, _, _, _, _, _, _);
                        merge_fractions rdcss_descriptor_success(d, _);
                        if (a1Prophecy == o1) {
                            d->success = true;
                            ghost_assoc_list_update(bsList, a2, n2);
                            split_fraction rdcss_descriptor_success(d, _);
                            close rdcss_cell(dsList)(a2, n2);
                            foreach_assoc_unseparate(bs, a2);
                        } else {
                            split_fraction rdcss_descriptor_success(d, _);
                            close rdcss_cell(dsList)(a2, o2);
                            foreach_assoc_unseparate_nochange(bs, a2);
                        }
                        split_fraction tracked_cas_prediction(tracker, 0, _);
                    }
                    split_fraction rdcss_descriptor_done(d, true);
                }
            }
            close rdcss_descriptor(asList, bsList, unsep)(d);
            foreach_unseparate(ds, d);
            assert ghost_assoc_list(bsList, ?bs1);
            close rdcss(id, unsep, aas, bs1);
            unsep();
            close atomic_load_pointer_context_post(context1)();
        }
        @*/
        //@ close atomic_load_pointer_context_pre(context1)(inv, a1, a1Prophecy);
        //@ produce_lemma_function_pointer_chunk(context1);
        r = atomic_load_pointer(d->a1);
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
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
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
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
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
            open rdcss(id, unsep, ?as, ?bs);
            merge_fractions ghost_cell3(id, _, _, _);
            split_fraction ghost_cell3(id, _, _, _);
            ghost_list_member_handle_lemma();
            assert ghost_list(dsList, ?ds);
            foreach_separate(ds, d);
            open rdcss_descriptor(asList, bsList, unsep)(d);
            merge_fractions descr(d, _, _, _, _, _, _, _);
            ghost_assoc_list_member_handle_lemma(bsList, a2);
            foreach_assoc_separate(bs, a2);
            open rdcss_cell(dsList)(a2, ?abstractValue);
            assert [_]pointer(a2, ?w);
            if (w == (void *)((uintptr_t)d | 1)) {
                bitand_bitor_lemma((uintptr_t)d, 1);
                merge_fractions rdcss_descriptor_detached(d, _);
                merge_fractions descr(d, _, _, _, _, _, _, _);
                merge_fractions pointer(a2, _);
                merge_fractions rdcss_descriptor_success(d, ?success);
                if (a2Prophecy == w) {
                    open prediction(?w0);
                    if (w0 == (a1Prophecy == o1 ? n2 : o2)) {
                        merge_fractions rdcss_descriptor_done(d, _);
                        merge_fractions tracked_cas_prediction(tracker, 0, _);
                        split_fraction tracked_cas_prediction(tracker, 0, _);
                        aop(0, w0);
                        d->detached = true;
                        split_fraction rdcss_descriptor_detached(d, true);
                        w = success ? n2 : o2;
                        leak [_]ghost_list_member_handle(dsList, d);
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
                assert [_]d->detached |-> ?detached;
                if (detached) {
                    split_fraction rdcss_descriptor_detached(d, _);
                } else {
                    merge_fractions pointer(a2, _); 
                }
            }
            close rdcss_cell(dsList)(a2, abstractValue);
            foreach_assoc_unseparate_nochange(bs, a2);
            split_fraction descr(d, _, _, _, _, _, _, _);
            close rdcss_descriptor(asList, bsList, unsep)(d);
            foreach_unseparate(ds, d);
            close rdcss(id, unsep, as, bs);
            unsep();
            close tracked_cas_ctxt_post(context2)();
        }
        @*/
        //@ close tracked_cas_ctxt_pre(context2)(tracker, inv, a2, (void *)((uintptr_t)d | 1), v, a2Prophecy);
        //@ produce_lemma_function_pointer_chunk(context2);
        tracked_cas(d->tracker, d->a2, (void *)((uintptr_t)d | 1), v);
        //@ leak is_tracked_cas_ctxt(context2);
        //@ open tracked_cas_ctxt_post(context2)();
    }
    //@ close [fDescr]descr(d, a1, o1, a2, o2, n2, tracker, op);
    //@ merge_fractions descr(d, _, _, _, _, _, _, _);
}

void *rdcss(void **a1, void *o1, void **a2, void *o2, void *n2)
    /*@
    requires
        true == (((uintptr_t)o2 & 1) == 0) &*&
        true == (((uintptr_t)n2 & 1) == 0) &*&
        [?f]atomic_space(?inv) &*&
        is_rdcss_separate_lemma(?sep) &*& is_rdcss_unseparate_lemma(?unsep) &*& rdcss_separate_lemma(sep)(?id, inv, unsep) &*&
        is_rdcss_as_membership_lemma(?asMem) &*& rdcss_as_membership_lemma(asMem)(unsep, a1) &*&
        is_rdcss_bs_membership_lemma(?bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
        is_rdcss_operation_lemma(?op) &*& rdcss_operation_pre(op)(unsep, a1, o1, a2, o2, n2);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
        is_rdcss_as_membership_lemma(asMem) &*& rdcss_as_membership_lemma(asMem)(unsep, a1) &*&
        is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
        is_rdcss_operation_lemma(op) &*& rdcss_operation_post(op)(result);
    @*/
{
    struct cas_tracker *tracker = create_cas_tracker();
    struct rdcss_descriptor *d = malloc(sizeof(struct rdcss_descriptor));
    //@ assume(((uintptr_t)d & 1) == 0);
    if (d == 0) abort();
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
loop:
    /*@
    invariant
        true == (((uintptr_t)d & 1) == 0) &*&
        [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*& d->done |-> false &*& d->success |-> false &*& d->detached |-> false &*& d->disposed |-> false &*&
        cas_tracker(tracker, 0) &*&
        malloc_block_rdcss_descriptor(d) &*&
        [f]atomic_space(inv) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
        is_rdcss_as_membership_lemma(asMem) &*& rdcss_as_membership_lemma(asMem)(unsep, a1) &*&
        is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
        is_rdcss_operation_lemma(op) &*& rdcss_operation_pre(op)(unsep, a1, o1, a2, o2, n2);
    @*/
    //@ void *prophecy = create_prophecy_pointer();
    void *r = 0;
    {
        /*@
        predicate_family_instance atomic_compare_and_store_pointer_context_pre(context)(predicate() inv_, void **p, void *old, void *new, void *prophecy_) =
            inv_ == inv &*& p == a2 &*& old == o2 &*& new == (void *)((uintptr_t)d | 1) &*& prophecy_ == prophecy &*&
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
            is_rdcss_as_membership_lemma(asMem) &*& rdcss_as_membership_lemma(asMem)(unsep, a1) &*&
            is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
            is_rdcss_operation_lemma(op) &*& rdcss_operation_pre(op)(unsep, a1, o1, a2, o2, n2) &*&
            [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
            cas_tracker(tracker, 0) &*&
            d->done |-> false &*& d->success |-> false &*& d->detached |-> false &*& d->disposed |-> false;
        
        predicate_family_instance atomic_compare_and_store_pointer_context_post(context)() =
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
            is_rdcss_as_membership_lemma(asMem) &*& rdcss_as_membership_lemma(asMem)(unsep, a1) &*&
            is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
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
                    is_rdcss_operation_lemma(op) &*& rdcss_operation_pre(op)(unsep, a1, o1, a2, o2, n2) &*&
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
            open rdcss(_, _, ?as, ?bs);
            split_fraction ghost_cell3(id, ?asList, ?bsList, ?dsList);
            assert ghost_list(dsList, ?ds);
            foreach_assoc_separate(bs, a2);
            open rdcss_cell(dsList)(a2, ?abstractValue);
            aop();
            if (prophecy == o2) {
                // We install the descriptor.
                split_fraction rdcss_descriptor_detached(d, false);
                ghost_list_add(dsList, d);
                split_fraction ghost_list_member_handle(dsList, d);
                bitand_bitor_lemma((uintptr_t)d, 1);
                split_fraction pointer(a2, _);
                split_fraction rdcss_descriptor_success(d, _);
                split_fraction descr(d, _, _, _, _, _, _, _);
                close rdcss_cell(dsList)(a2, o2);
                foreach_assoc_unseparate_nochange(bs, a2);
                split_fraction descr(d, _, _, _, _, _, _, _);
                split_fraction rdcss_descriptor_disposed(d, false);
                ghost_list_create_member_handle(asList, a1);
                ghost_assoc_list_create_member_handle(bsList, a2);
                close rdcss_descriptor(asList, bsList, unsep)(d);
                close foreach(cons((void *)d, ds), rdcss_descriptor(asList, bsList, unsep));
                close rdcss(id, unsep, as, bs);
            } else if (((uintptr_t)prophecy & 1) == 0) {
                // Failure.
                close rdcss_cell(dsList)(a2, prophecy);
                foreach_assoc_unseparate_nochange(bs, a2);
                close rdcss(id, unsep, as, bs);
                op();
                leak cas_tracker(tracker, 0);
                leak [_]d->done |-> _;
                leak [_]d->success |-> _;
                leak [_]d->detached |-> _;
                leak [_]d->disposed |-> _;
                leak [_]ghost_cell3(id, _, _, _);
                leak [_]descr(d, _, _, _, _, _, _, _);
            } else {
                // We bumped into another descriptor. Extract a chunk saying that it's in the atomic space.
                split_fraction ghost_list_member_handle(dsList, (void *)((uintptr_t)prophecy & ~1));
                split_fraction descr((void *)((uintptr_t)prophecy & ~1), _, _, _, _, _, _, _);
                close rdcss_cell(dsList)(a2, abstractValue);
                foreach_assoc_unseparate_nochange(bs, a2);
                close rdcss(id, unsep, as, bs);
            }
            unsep();
            close atomic_compare_and_store_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_compare_and_store_pointer_context_pre(context)(inv, a2, o2, (void *)((uintptr_t)d | 1), prophecy);
        //@ produce_lemma_function_pointer_chunk(context);
        r = atomic_compare_and_store_pointer(a2, o2, (void *)((uintptr_t)d | 1));
        //@ leak is_atomic_compare_and_store_pointer_context(context);
        //@ open atomic_compare_and_store_pointer_context_post(context)();
    }
    if (((uintptr_t)r & 1) != 0) {
        rdcss_complete((void *)((uintptr_t)r & ~1));
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
                is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
                [_]ghost_cell3(id, ?asList, ?bsList, ?dsList) &*&
                [_]ghost_list_member_handle(dsList, d) &*&
                [_]descr(d, a1, o1, a2, o2, n2, tracker, op) &*&
                [1/2]d->disposed |-> false &*&
                [_]d->detached |-> true;
            predicate_family_instance atomic_noop_context_post(context)() =
                is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
                is_rdcss_operation_lemma(op) &*& rdcss_operation_post(op)(r);
            lemma void context() : atomic_noop_context
                requires atomic_noop_context_pre(context)(?inv_) &*& inv_();
                ensures atomic_noop_context_post(context)() &*& inv_();
            {
                open atomic_noop_context_pre(context)(_);
                sep();
                open rdcss(id, unsep, ?as, ?bs);
                merge_fractions ghost_cell3(id, ?asList, ?bsList, ?dsList);
                ghost_list_member_handle_lemma();
                assert ghost_list(dsList, ?ds);
                foreach_separate(ds, d);
                open rdcss_descriptor(asList, bsList, unsep)(d);
                merge_fractions descr(d, _, _, _, _, _, _, _);
                merge_fractions rdcss_descriptor_disposed(d, _);
                merge_fractions rdcss_descriptor_detached(d, _);
                d->disposed = true;
                split_fraction rdcss_descriptor_disposed(d, _);
                close rdcss_descriptor(asList, bsList, unsep)(d);
                foreach_unseparate(ds, d);
                close rdcss(id, unsep, as, bs);
                unsep();
                close atomic_noop_context_post(context)();
                leak [_]d->disposed |-> _;
                leak [_]ghost_list_member_handle(dsList, d);
            }
            @*/
            //@ close atomic_noop_context_pre(context)(inv);
            //@ produce_lemma_function_pointer_chunk(context);
            atomic_noop();
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

/*@

predicate_family rdcss_read_operation_pre(void *op)(rdcss_unseparate_lemma *unsep, void **a2);
predicate_family rdcss_read_operation_post(void *op)(void *result);

typedef lemma void *rdcss_read_operation_lemma();
    requires rdcss_read_operation_pre(this)(?unsep, ?a2) &*& rdcss_unseparate_lemma(unsep)(?id, ?inv, ?sep, ?aas, ?avs, ?bs);
    ensures
        rdcss_read_operation_post(this)(result) &*& mem_assoc(a2, bs) == true &*& result == assoc(a2, bs) &*&
        rdcss_unseparate_lemma(unsep)(id, inv, sep, aas, avs, bs);

@*/

void *rdcss_read(void **a2)
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_rdcss_separate_lemma(?sep) &*& is_rdcss_unseparate_lemma(?unsep) &*& rdcss_separate_lemma(sep)(?id, inv, unsep) &*&
        is_rdcss_bs_membership_lemma(?bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
        is_rdcss_read_operation_lemma(?op) &*& rdcss_read_operation_pre(op)(unsep, a2);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
        is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
        is_rdcss_read_operation_lemma(op) &*& rdcss_read_operation_post(op)(result);
    @*/
{
loop:
    /*@
    invariant
        [f]atomic_space(inv) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
        is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
        is_rdcss_read_operation_lemma(op) &*& rdcss_read_operation_pre(op)(unsep, a2);
    @*/
    void *r = 0;
    //@ void *prophecy = create_prophecy_pointer();
    {
        /*@
        predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv_, void **pp, void *prophecy_) =
            inv_ == inv &*& pp == a2 &*& prophecy_ == prophecy &*&
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
            is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
            is_rdcss_read_operation_lemma(op) &*& rdcss_read_operation_pre(op)(unsep, a2);
        predicate_family_instance atomic_load_pointer_context_post(context)() =
            is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
            is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
            is_rdcss_read_operation_lemma(op) &*&
            true == (((uintptr_t)prophecy & 1) == 0) ?
                rdcss_read_operation_post(op)(prophecy)
            :
                rdcss_read_operation_pre(op)(unsep, a2) &*&
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
            open rdcss(id, unsep, ?as, ?bs);
            assert [_]ghost_cell3(id, ?asList, ?bsList, ?dsList);
            assert ghost_list(dsList, ?ds);
            foreach_assoc_separate(bs, a2);
            open rdcss_cell(dsList)(a2, ?abstractValue);
            aop();
            if (((uintptr_t)prophecy & 1) == 0) {
                op();
            } else {
                split_fraction ghost_cell3(id, asList, bsList, dsList);
                split_fraction ghost_list_member_handle(dsList, (void *)((uintptr_t)prophecy & ~1));
                split_fraction descr((void *)((uintptr_t)prophecy & ~1), _, _, _, _, _, _, _);
            }
            close rdcss_cell(dsList)(a2, abstractValue);
            foreach_assoc_unseparate_nochange(bs, a2);
            close rdcss(id, unsep, as, bs);
            unsep();
            close atomic_load_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_load_pointer_context_pre(context)(inv, a2, prophecy);
        //@ produce_lemma_function_pointer_chunk(context);
        r = atomic_load_pointer(a2);
        //@ leak is_atomic_load_pointer_context(context);
        //@ open atomic_load_pointer_context_post(context)();
    }
    if (((uintptr_t)r & 1) != 0) {
        rdcss_complete((void *)((uintptr_t)r & ~1));
        //@ leak [_]rdcss_descriptor_detached(_, _);
        //@ leak [_]ghost_cell3(_, _, _, _);
        //@ leak [_]ghost_list_member_handle(_, _);
        //@ leak [_]descr(_, _, _ ,_, _, _, _, _);
        goto loop;
    }
    return r;
}

// TODO: We need a CAS that allows spurious failure.

/*@

predicate_family rdcss_cas_pre(void *op)(rdcss_unseparate_lemma *unsep, void **a2, void *o2, void *n2);
predicate_family rdcss_cas_post(void *op)(void *result);

typedef lemma void *rdcss_cas_lemma();
    requires rdcss_cas_pre(this)(?unsep, ?a2, ?o2, ?n2) &*& rdcss_unseparate_lemma(unsep)(?id, ?inv, ?sep, ?aas, ?avs, ?bs);
    ensures
        rdcss_cas_post(this)(result) &*& mem_assoc(a2, bs) == true &*& result == assoc(a2, bs) &*&
        assoc(a2, bs) == o2 ?
            rdcss_unseparate_lemma(unsep)(id, inv, sep, aas, avs, update(bs, a2, n2))
        :
            rdcss_unseparate_lemma(unsep)(id, inv, sep, aas, avs, bs);

@*/

void *rdcss_compare_and_store(void **a2, void *o2, void *n2)
    /*@
    requires
        true == (((uintptr_t)o2 & 1) == 0) &*&
        true == (((uintptr_t)n2 & 1) == 0) &*&
        [?f]atomic_space(?inv) &*&
        is_rdcss_separate_lemma(?sep) &*& is_rdcss_unseparate_lemma(?unsep) &*& rdcss_separate_lemma(sep)(?id, inv, unsep) &*&
        is_rdcss_bs_membership_lemma(?bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
        is_rdcss_cas_lemma(?op) &*& rdcss_cas_pre(op)(unsep, a2, o2, n2);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_rdcss_separate_lemma(sep) &*& is_rdcss_unseparate_lemma(unsep) &*& rdcss_separate_lemma(sep)(id, inv, unsep) &*&
        is_rdcss_bs_membership_lemma(bsMem) &*& rdcss_bs_membership_lemma(bsMem)(unsep, a2) &*&
        is_rdcss_cas_lemma(op) &*& rdcss_cas_post(op)(result);
    @*/
{
    //@ assume(false);
    void *r = atomic_compare_and_store_pointer(a2, o2, n2);
    return r;
}
