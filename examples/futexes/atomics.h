#ifndef STDATOMIC_H
#define STDATOMIC_H

/*@

predicate call_perm_top();

predicate atomic_space(void *name, predicate() inv;);

lemma void create_atomic_space(void *name, predicate() inv);
    requires inv();
    ensures atomic_space(name, inv);

lemma void destroy_atomic_space();
    requires atomic_space(_, ?inv);
    ensures inv();

predicate atomic_spaces(list<pair<void *, predicate()> > spaces);

lemma void open_atomic_space(void *name, predicate() inv);
    requires atomic_spaces(?spaces) &*& [?f]atomic_space(name, inv) &*& !mem(pair(name, inv), spaces);
    ensures atomic_spaces(cons(pair(name, inv), spaces)) &*& [f]atomic_space(name, inv) &*& inv();

lemma void close_atomic_space(void *name, predicate() inv);
    requires atomic_spaces(?spaces) &*& inv() &*& mem(pair(name, inv), spaces) == true;
    ensures atomic_spaces(remove(pair(name, inv), spaces));

// A fixpoint that may be useful in clients of this header.
fixpoint bool space_name_lt(void *name1, pair<void *, predicate()> space) { return func_lt(fst(space), name1); }

fixpoint bool func_gt(void *name1, void *name2) { return func_lt(name2, name1); }

@*/

/*@

typedef lemma void atomic_noop_ghost_op(predicate() pre, predicate() post)();
    requires atomic_spaces({}) &*& pre();
    ensures atomic_spaces({}) &*& post();

lemma void atomic_noop();
    nonghost_callers_only
    requires is_atomic_noop_ghost_op(?ghop, ?pre, ?post) &*& pre();
    ensures is_atomic_noop_ghost_op(ghop, pre, post) &*& post();

@*/

//@ predicate futex_word(int *word; int value);

/*@

typedef lemma void atomic_weak_compare_and_set_futex_word_op(int *object, int oldValue, int newValue, predicate() P, predicate(bool) Q)();
    requires [?f]futex_word(object, ?value) &*& P() &*& value != oldValue || f == 1;
    ensures [f]futex_word(object, value == oldValue ? newValue : value) &*& Q(value == oldValue);

typedef lemma void atomic_weak_compare_and_set_futex_word_ghost_op(int *object, int oldValue, int newValue, predicate() pre, predicate(bool) post)();
    requires atomic_spaces({}) &*& is_atomic_weak_compare_and_set_futex_word_op(?op, object, oldValue, newValue, ?P, ?Q) &*& P() &*& pre();
    ensures atomic_spaces({}) &*& is_atomic_weak_compare_and_set_futex_word_op(op, object, oldValue, newValue, P, Q) &*& Q(?success) &*& post(success);

@*/

bool atomic_weak_compare_and_set_futex_word(int *object, int oldValue, int newValue);
//@ requires is_atomic_weak_compare_and_set_futex_word_ghost_op(?ghop, object, oldValue, newValue, ?pre, ?post) &*& pre();
//@ ensures result ? post(true) : exists<bool>(?spurious) &*& spurious ? pre() &*& call_perm_top() : post(false);
//@ terminates;

/*@

typedef lemma void atomic_store_futex_word_op(int *object, int value, predicate() P, predicate() Q)();
    requires futex_word(object, _) &*& P();
    ensures futex_word(object, value) &*& Q();

typedef lemma void atomic_store_futex_word_ghost_op(int *object, int value, predicate() pre, predicate() post)();
    requires atomic_spaces({}) &*& is_atomic_store_futex_word_op(?op, object, value, ?P, ?Q) &*& P() &*& pre();
    ensures atomic_spaces({}) &*& is_atomic_store_futex_word_op(op, object, value, P, Q) &*& Q() &*& post();

@*/

void atomic_store_futex_word(int *object, int value);
//@ requires is_atomic_store_futex_word_ghost_op(?ghop, object, value, ?pre, ?post) &*& pre();
//@ ensures post();
//@ terminates;

#endif
