#ifndef LCSET_H
#define LCSET_H

#include "atomics.h"

struct set;

/*@

predicate set(struct set *set;);
predicate set_atomic(struct set *set, list<int> values);

@*/

struct set *create_set();
    //@ requires true;
    //@ ensures set(result) &*& set_atomic(result, nil);

void dispose_set(struct set *set);
    //@ requires set(set) &*& set_atomic(set, ?values);
    //@ ensures true;

/*@

predicate_family set_sep(void *sep)(any info, struct set *set, predicate() inv, set_unsep *unsep);
predicate_family set_unsep(void *unsep)(any info, struct set *set, predicate() inv, set_sep *sep, list<int> values);

typedef lemma void set_sep();
    requires set_sep(this)(?info, ?set, ?inv, ?unsep) &*& inv();
    ensures set_unsep(unsep)(info, set, inv, this, ?values) &*& set_atomic(set, values);

typedef lemma void set_unsep();
    requires set_unsep(this)(?info, ?set, ?inv, ?sep, ?values) &*& set_atomic(set, values);
    ensures set_sep(sep)(info, set, inv, this) &*& inv();

fixpoint bool mem_sorted(int e, list<int> xs) {
    switch (xs) {
        case nil: return false;
        case cons(x, xs0): return x <= e && (x == e || mem_sorted(e, xs0));
    }
}

fixpoint list<int> add_sorted(int e, list<int> xs) {
    switch (xs) {
        case nil: return cons(e, nil);
        case cons(x, xs0): return e < x ? cons(e, xs) : e == x ? xs : cons(x, add_sorted(e, xs0));
    }
}

@*/

/*@

predicate_family set_contains_pre(void *op)(set_unsep *unsep, any info, int e);
predicate_family set_contains_post(void *op)(bool result);

typedef lemma void set_contains();
    requires set_contains_pre(this)(?unsep, ?info, ?e) &*& set_unsep(unsep)(info, ?set, ?inv, ?sep, ?values);
    ensures set_contains_post(this)(mem_sorted(e, values)) &*& set_unsep(unsep)(info, set, inv, sep, values);

@*/

bool contains(struct set *set, int e);
    /*@
    requires
        INT_MIN < e &*& e < INT_MAX &*&
        [?f]atomic_space(?inv) &*&
        [?fSet]set(set) &*&
        is_set_sep(?sep) &*& is_set_unsep(?unsep) &*& set_sep(sep)(?info, set, inv, unsep) &*&
        is_set_contains(?op) &*& set_contains_pre(op)(unsep, info, e);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        [fSet]set(set) &*&
        is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
        is_set_contains(op) &*& set_contains_post(op)(result);
    @*/

/*@

predicate_family set_add_pre(void *op)(set_unsep *unsep, any info, int e);
predicate_family set_add_post(void *op)(bool result);

typedef lemma void set_add();
    requires set_add_pre(this)(?unsep, ?info, ?e) &*& set_unsep(unsep)(info, ?set, ?inv, ?sep, ?values);
    ensures set_add_post(this)(!mem_sorted(e, values)) &*& set_unsep(unsep)(info, set, inv, sep, add_sorted(e, values));

@*/

bool add(struct set *set, int e);
    /*@
    requires
        INT_MIN < e &*& e < INT_MAX &*&
        [?f]atomic_space(?inv) &*&
        [?fSet]set(set) &*&
        is_set_sep(?sep) &*& is_set_unsep(?unsep) &*& set_sep(sep)(?info, set, inv, unsep) &*&
        is_set_add(?op) &*& set_add_pre(op)(unsep, info, e);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        [fSet]set(set) &*&
        is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
        is_set_add(op) &*& set_add_post(op)(result);
    @*/

/*@

fixpoint list<int> remove_sorted(int e, list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return e < x ? xs : e == x ? xs0 : cons(x, remove_sorted(e, xs0));
    }
}

predicate_family set_remove_pre(void *op)(set_unsep *unsep, any info, int e);
predicate_family set_remove_post(void *op)(bool success);

typedef lemma void set_remove();
    requires set_remove_pre(this)(?unsep, ?info, ?e) &*& set_unsep(unsep)(info, ?set, ?inv, ?sep, ?xs);
    ensures set_remove_post(this)(mem_sorted(e, xs)) &*& set_unsep(unsep)(info, set, inv, sep, remove_sorted(e, xs));

@*/

bool remove(struct set *set, int e);
    /*@
    requires
        INT_MIN < e &*& e < INT_MAX &*&
        [?f]atomic_space(?inv) &*&
        [?fSet]set(set) &*&
        is_set_sep(?sep) &*& is_set_unsep(?unsep) &*& set_sep(sep)(?info, set, inv, unsep) &*&
        is_set_remove(?op) &*& set_remove_pre(op)(unsep, info, e);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        [fSet]set(set) &*&
        is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
        is_set_remove(op) &*& set_remove_post(op)(result);
    @*/

#endif