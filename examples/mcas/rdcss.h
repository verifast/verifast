#ifndef RDCSS_H
#define RDCSS_H

#include "atomics.h"
//@ #include "assoc_list.gh"

/*@

predicate rdcss(int id, rdcss_unseparate_lemma *unsep, any info, list<void *> aas, list<pair<void *, void *> > bs);

predicate_family rdcss_separate_lemma(void *sep)(any info, int id, predicate() inv, rdcss_unseparate_lemma *unsep);
predicate_family rdcss_unseparate_lemma(void *unsep)(any info, int id, predicate() inv, rdcss_separate_lemma *sep, list<void *> aas, list<void *> avs, list<pair<void *, void *> > bs);

typedef lemma void rdcss_separate_lemma();
    requires rdcss_separate_lemma(this)(?info, ?id, ?inv, ?unsep) &*& inv();
    ensures rdcss_unseparate_lemma(unsep)(info, id, inv, this, ?aas, ?avs, ?bs) &*& foreach_assoc(zip(aas, avs), pointer) &*& rdcss(id, unsep, info, aas, bs);

typedef lemma void rdcss_unseparate_lemma();
    requires rdcss_unseparate_lemma(this)(?info, ?id, ?inv, ?sep, ?aas, ?avs, ?bs) &*& foreach_assoc(zip(aas, avs), pointer) &*& rdcss(id, this, info, aas, bs);
    ensures rdcss_separate_lemma(sep)(info, id, inv, this) &*& inv();

predicate_family rdcss_as_membership_lemma(void *mem)(rdcss_unseparate_lemma *unsep, any info, void **a1);

typedef lemma void rdcss_as_membership_lemma();
    requires rdcss_as_membership_lemma(this)(?unsep, ?info, ?a1) &*& rdcss_unseparate_lemma(unsep)(info, ?id, ?inv, ?sep, ?aas, ?avs, ?bs);
    ensures rdcss_as_membership_lemma(this)(unsep, info, a1) &*& rdcss_unseparate_lemma(unsep)(info, id, inv, sep, aas, avs, bs) &*& mem((void *)a1, aas) == true;

predicate_family rdcss_bs_membership_lemma(void *mem)(rdcss_unseparate_lemma *unsep, any info, void **a2);

typedef lemma void rdcss_bs_membership_lemma();
    requires rdcss_bs_membership_lemma(this)(?unsep, ?info, ?a2) &*& rdcss_unseparate_lemma(unsep)(info, ?id, ?inv, ?sep, ?aas, ?avs, ?bs);
    ensures rdcss_bs_membership_lemma(this)(unsep, info, a2) &*& rdcss_unseparate_lemma(unsep)(info, id, inv, sep, aas, avs, bs) &*& mem_assoc(a2, bs) == true;

@*/

/*@

lemma int create_rdcss(rdcss_unseparate_lemma *unsep, any info);
    requires true;
    ensures rdcss(result, unsep, info, nil, nil);

lemma void rdcss_add_a(void *aa);
    requires rdcss(?id, ?unsep, ?info, ?aas, ?bs);
    ensures rdcss(id, unsep, info, cons(aa, aas), bs);

lemma void rdcss_add_b(void *ba);
    requires rdcss(?id, ?unsep, ?info, ?aas, ?bs) &*& pointer(ba, ?bv) &*& true == (((uintptr_t)bv & 1) == 0) &*& !mem_assoc(ba, bs);
    ensures rdcss(id, unsep, info, aas, cons(pair(ba, bv), bs));

@*/

/*@

predicate_family rdcss_operation_pre(void *op)(rdcss_unseparate_lemma *unsep, any info, void **a1, void *o1, void **a2, void *o2, void *n2);
predicate_family rdcss_operation_post(void *op)(void *result);

typedef lemma void *rdcss_operation_lemma();
    requires rdcss_operation_pre(this)(?unsep, ?info, ?a1, ?o1, ?a2, ?o2, ?n2) &*& rdcss_unseparate_lemma(unsep)(info, ?id, ?inv, ?sep, ?aas, ?avs, ?bs);
    ensures
        rdcss_operation_post(this)(result) &*& mem((void *)a1, aas) == true &*& mem_assoc(a2, bs) == true &*& result == assoc(a2, bs) &*&
        assoc(a1, zip(aas, avs)) == o1 && assoc(a2, bs) == o2 ?
            rdcss_unseparate_lemma(unsep)(info, id, inv, sep, aas, avs, update_assoc(bs, a2, n2))
        :
            rdcss_unseparate_lemma(unsep)(info, id, inv, sep, aas, avs, bs);

@*/

void *rdcss(void **a1, void *o1, void **a2, void *o2, void *n2);
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

/*@

predicate_family rdcss_read_operation_pre(void *op)(rdcss_unseparate_lemma *unsep, any info, void **a2);
predicate_family rdcss_read_operation_post(void *op)(void *result);

typedef lemma void *rdcss_read_operation_lemma();
    requires rdcss_read_operation_pre(this)(?unsep, ?info, ?a2) &*& rdcss_unseparate_lemma(unsep)(info, ?id, ?inv, ?sep, ?aas, ?avs, ?bs);
    ensures
        rdcss_read_operation_post(this)(result) &*& mem_assoc(a2, bs) == true &*& result == assoc(a2, bs) &*&
        rdcss_unseparate_lemma(unsep)(info, id, inv, sep, aas, avs, bs);

@*/

void *rdcss_read(void **a2);
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

/*@

predicate_family rdcss_cas_pre(void *op)(rdcss_unseparate_lemma *unsep, any info, void **a2, void *o2, void *n2);
predicate_family rdcss_cas_post(void *op)(bool success);

typedef lemma void rdcss_cas_lemma(bool success);
    requires
        rdcss_cas_pre(this)(?unsep, ?info, ?a2, ?o2, ?n2) &*&
        rdcss_unseparate_lemma(unsep)(info, ?id, ?inv, ?sep, ?aas, ?avs, ?bs) &*&
        mem_assoc(a2, bs) == true &*&
        success ? assoc(a2, bs) == o2 : true;
    ensures
        rdcss_cas_post(this)(success) &*&
        rdcss_unseparate_lemma(unsep)(info, id, inv, sep, aas, avs, ?bs1) &*&
        success ?
            bs1 == update_assoc(bs, a2, n2)
        :
            bs1 == bs;

@*/

bool rdcss_compare_and_store(void **a2, void *o2, void *n2);
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

#endif