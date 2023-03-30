#ifndef STDATOMIC_H
#define STDATOMIC_H

/*@

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
    requires atomic_spaces(?spaces) &*& inv();
    ensures atomic_spaces(remove(pair(name, inv), spaces));

// A fixpoint that may be useful in clients of this header.
fixpoint bool space_name_lt(void *name1, pair<void *, predicate()> space) { return func_lt(fst(space), name1); }

@*/

/*@

typedef lemma void atomic_load_int_op(int *object, predicate() P, predicate(int) Q)();
    requires [?f]*object |-> ?value &*& P();
    ensures [f]*object |-> value &*& Q(value);

typedef lemma void atomic_load_int_ghost_op(void *name, predicate() inv, int *object, predicate() pre, predicate(int) post, int callerThread)();
    requires inv() &*& is_atomic_load_int_op(?op, object, ?P, ?Q) &*& P() &*& pre() &*& currentThread == callerThread &*& atomic_spaces({pair(name, inv)});
    ensures inv() &*& is_atomic_load_int_op(op, object, P, Q) &*& Q(?value) &*& post(value) &*& atomic_spaces({pair(name, inv)});

@*/

int atomic_load_int(int *object);
    /*@
    requires
        [?frac]atomic_space(?name, ?inv) &*&
        is_atomic_load_int_ghost_op(?ghop, name, inv, object, ?pre, ?post, currentThread) &*& pre();
    @*/
    /*@
    ensures
        [frac]atomic_space(name, inv) &*&
        is_atomic_load_int_ghost_op(ghop, name, inv, object, pre, post, currentThread) &*& post(result);
    @*/
    //@ terminates;

/*@

typedef lemma void atomic_store_int_op(int *object, int desired, predicate() P, predicate() Q)();
    requires *object |-> _ &*& P();
    ensures *object |-> desired &*& Q();

typedef lemma void atomic_store_int_ghost_op(void *name, predicate() inv, int *object, int desired, predicate() pre, predicate() post, int callerThread)();
    requires inv() &*& is_atomic_store_int_op(?op, object, desired, ?P, ?Q) &*& P() &*& pre() &*& currentThread == callerThread &*& atomic_spaces({pair(name, inv)});
    ensures inv() &*& is_atomic_store_int_op(op, object, desired, P, Q) &*& Q() &*& post() &*& atomic_spaces({pair(name, inv)});

@*/

void atomic_store_int(int *object, int desired);
    /*@
    requires
        [?frac]atomic_space(?name, ?inv) &*&
        is_atomic_store_int_ghost_op(?ghop, name, inv, object, desired, ?pre, ?post, currentThread) &*& pre();
    @*/
    /*@
    ensures
        [frac]atomic_space(name, inv) &*&
        is_atomic_store_int_ghost_op(ghop, name, inv, object, desired, pre, post, currentThread) &*& post();
    @*/
    //@ terminates;

/*@

typedef lemma void compare_and_swap_int_op
    (int *object, int oldValue, int newValue, predicate() P, predicate(int) Q)();
    requires *object |-> ?old &*& P();
    ensures *object |-> (old == oldValue ? newValue : old) &*& Q(old);

typedef lemma void compare_and_swap_int_ghost_op
    (void *name, predicate() inv, int *object, int oldValue, int newValue,
     predicate() pre, predicate(int) post, int callerThread)();
    requires
        inv() &*&
        is_compare_and_swap_int_op(?op, object, oldValue, newValue, ?P, ?Q) &*&
        P() &*& pre() &*& callerThread == currentThread &*&
        atomic_spaces({pair(name, inv)});
    ensures
        inv() &*&
        is_compare_and_swap_int_op(op, object, oldValue, newValue, P, Q) &*&
        Q(?result) &*& post(result) &*&
        atomic_spaces({pair(name, inv)});
 
@*/

int compare_and_swap_int(int *object, int oldValue, int newValue);
    /*@
    requires
        [?frac]atomic_space(?name, ?inv) &*&
        is_compare_and_swap_int_ghost_op(?ghop, name, inv, object, oldValue, newValue, ?pre, ?post, currentThread) &*&
        pre();
    @*/
    /*@
    ensures
        [frac]atomic_space(name, inv) &*&
        post(result);
    @*/
    //@ terminates;

#endif
