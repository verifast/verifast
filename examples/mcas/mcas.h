#ifndef MCAS_H
#define MCAS_H

#include "bool.h"
#include "stdlib.h"
#include "list.h"
#include "assoc_list.h"
#include "atomics.h"

struct mcas_entry {
    void **a;
    void *o;
    void *n;
};

/*@

predicate entries(int count, struct mcas_entry *aes; list<pair<void *, pair<void *, void *> > > es) =
    count <= 0 ?
        es == nil &*& count == 0
    :
        aes->a |-> ?a &*& aes->o |-> ?o &*& aes->n |-> ?n &*& struct_mcas_entry_padding(aes) &*&
        true == (((uintptr_t)o & 1) == 0) &*&
        true == (((uintptr_t)o & 2) == 0) &*&
        true == (((uintptr_t)n & 1) == 0) &*&
        true == (((uintptr_t)n & 2) == 0) &*&
        entries(count - 1, aes + 1, ?es0) &*&
        es == cons(pair((void *)a, pair(o, n)), es0);

predicate mcas(int id, mcas_sep *sep, mcas_unsep *unsep, any mcasInfo, list<pair<void *, void *> > cs);

predicate_family mcas_sep(void *sep)(any mcasInfo, int id, predicate() inv, mcas_unsep *unsep);
predicate_family mcas_unsep(void *unsep)(any mcasInfo, int id, predicate() inv, mcas_sep *sep, list<pair<void *, void *> > cs);

typedef lemma void mcas_sep();
    requires mcas_sep(this)(?mcasInfo, ?id, ?inv, ?unsep) &*& inv();
    ensures mcas_unsep(unsep)(mcasInfo, id, inv, this, ?cs) &*& mcas(id, this, unsep, mcasInfo, cs);

typedef lemma void mcas_unsep();
    requires mcas_unsep(this)(?mcasInfo, ?id, ?inv, ?sep, ?cs) &*& mcas(id, sep, this, mcasInfo, cs);
    ensures mcas_sep(sep)(mcasInfo, id, inv, this) &*& inv();

predicate_family mcas_mem(void *mem)(mcas_unsep *unsep, any mcasInfo, list<pair<void *, pair<void *, void *> > > a);

fixpoint bool mem_es(list<pair<void *, pair<void *, void *> > > es, list<pair<void *, void *> > cs) {
    switch (es) {
        case nil: return true;
        case cons(e, es0): return mem_assoc(fst(e), cs) && mem_es(es0, cs);
    }
}

typedef lemma void mcas_mem();
    requires mcas_mem(this)(?unsep, ?mcasInfo, ?es) &*& mcas_unsep(unsep)(mcasInfo, ?id, ?inv, ?sep, ?cs);
    ensures mcas_mem(this)(unsep, mcasInfo, es) &*& mcas_unsep(unsep)(mcasInfo, id, inv, sep, cs) &*& mem_es(es, cs) == true;

predicate_family mcas_pre(void *op)(mcas_unsep *unsep, any mcasInfo, list<pair<void *, pair<void *, void *> > > es);
predicate_family mcas_post(void *op)(bool success);

fixpoint bool es_success(list<pair<void *, pair<void *, void *> > > es, list<pair<void *, void *> > cs) {
    switch (es) {
        case nil: return true;
        case cons(e, es0): return assoc(fst(e), cs) == fst(snd(e)) && es_success(es0, cs);
    }
}

fixpoint list<pair<void *, void *> > es_apply(list<pair<void *, pair<void *, void *> > > es, list<pair<void *, void *> > cs) {
    switch (es) {
        case nil: return cs;
        case cons(e, es0): return es_apply(es0, update_pairlist(cs, fst(e), snd(snd(e))));
    }
}

typedef lemma bool mcas_op();
    requires mcas_pre(this)(?unsep, ?mcasInfo, ?es) &*& mcas_unsep(unsep)(mcasInfo, ?id, ?inv, ?sep, ?cs);
    ensures
        es_success(es, cs) ?
            mcas_unsep(unsep)(mcasInfo, id, inv, sep, es_apply(es, cs)) &*& mcas_post(this)(true)
        :
            mcas_unsep(unsep)(mcasInfo, id, inv, sep, cs) &*& mcas_post(this)(false);

lemma int create_mcas(mcas_sep *sep, mcas_unsep *unsep, any mcasInfo);
    requires true;
    ensures mcas(result, sep, unsep, mcasInfo, nil);

lemma void mcas_add_cell(int id, void *a);
    requires mcas(id, ?sep, ?unsep, ?mcasInfo, ?cs) &*& !mem_assoc(a, cs) &*& pointer(a, ?v) &*& true == (((uintptr_t)v & 1) == 0) &*& true == (((uintptr_t)v & 2) == 0);
    ensures mcas(id, sep, unsep, mcasInfo, cons(pair(a, v), cs));

@*/

/*@

predicate_family mcas_cs_mem(void *csMem)(mcas_unsep *unsep, any mcasInfo, void *a);

typedef lemma void mcas_cs_mem();
    requires mcas_cs_mem(this)(?unsep, ?mcasInfo, ?a) &*& mcas_unsep(unsep)(mcasInfo, ?id, ?inv, ?sep, ?cs);
    ensures mcas_cs_mem(this)(unsep, mcasInfo, a) &*& mcas_unsep(unsep)(mcasInfo, id, inv, sep, cs) &*& mem_assoc(a, cs) == true;

predicate_family mcas_read_pre(void *rop)(mcas_unsep *unsep, any mcasInfo, void *a);
predicate_family mcas_read_post(void *rop)(void *result);

typedef lemma void mcas_read_op();
    requires mcas_read_pre(this)(?unsep, ?mcasInfo, ?a) &*& mcas_unsep(unsep)(mcasInfo, ?id, ?inv, ?sep, ?cs);
    ensures mcas_read_post(this)(assoc(a, cs)) &*& mcas_unsep(unsep)(mcasInfo, id, inv, sep, cs);

@*/

void *mcas_read(void *a);
    /*@
    requires
        is_mcas_sep(?sep) &*& is_mcas_unsep(?unsep) &*& mcas_sep(sep)(?mcasInfo, ?id, ?inv, unsep) &*&
        [?f]atomic_space(inv) &*&
        is_mcas_cs_mem(?csMem) &*& mcas_cs_mem(csMem)(unsep, mcasInfo, a) &*&
        is_mcas_read_op(?rop) &*& mcas_read_pre(rop)(unsep, mcasInfo, a);
    @*/
    /*@
    ensures
        is_mcas_sep(sep) &*& is_mcas_unsep(unsep) &*& mcas_sep(sep)(mcasInfo, id, inv, unsep) &*&
        [f]atomic_space(inv) &*&
        is_mcas_cs_mem(csMem) &*& mcas_cs_mem(csMem)(unsep, mcasInfo, a) &*&
        is_mcas_read_op(rop) &*& mcas_read_post(rop)(result);
    @*/

bool mcas(int n, struct mcas_entry *aes);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        entries(n, aes, ?es) &*&
        distinct(mapfst(es)) == true &*&
        is_mcas_sep(?sep) &*& is_mcas_unsep(?unsep) &*& mcas_sep(sep)(?mcasInfo, ?id, inv, unsep) &*&
        is_mcas_mem(?mem) &*& mcas_mem(mem)(unsep, mcasInfo, es) &*&
        is_mcas_op(?op) &*& mcas_pre(op)(unsep, mcasInfo, es);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_mcas_sep(sep) &*& is_mcas_unsep(unsep) &*& mcas_sep(sep)(mcasInfo, id, inv, unsep) &*&
        is_mcas_mem(mem) &*& mcas_mem(mem)(unsep, mcasInfo, es) &*&
        is_mcas_op(op) &*& mcas_post(op)(result);
    @*/

#endif