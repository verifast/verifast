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

fixpoint bool func_gt(void *f1, void *f2) { return func_lt(f2, f1); }

lemma void open_atomic_space(void *name, predicate() inv);
    requires atomic_spaces(?spaces) &*& [?f]atomic_space(name, inv) &*& !mem(pair(name, inv), spaces);
    ensures atomic_spaces(cons(pair(name, inv), spaces)) &*& [f]atomic_space(name, inv) &*& inv();

lemma void close_atomic_space(void *name, predicate() inv);
    requires atomic_spaces(?spaces) &*& inv() &*& mem(pair(name, inv), spaces) == true;
    ensures atomic_spaces(remove(pair(name, inv), spaces));

// A fixpoint that may be useful in clients of this header.
fixpoint bool space_name_lt(void *name1, pair<void *, predicate()> space) { return func_lt(fst(space), name1); }

typedef lemma void atomic_noop_ghost_op(predicate() pre, predicate() post, int callerThread)();
    requires atomic_spaces({}) &*& pre() &*& currentThread == callerThread;
    ensures atomic_spaces({}) &*& post();

lemma void atomic_noop();
    nonghost_callers_only
    requires is_atomic_noop_ghost_op(?ghop, ?pre, ?post, currentThread) &*& pre();
    ensures is_atomic_noop_ghost_op(ghop, pre, post, currentThread) &*& post();

@*/

/*@

predicate counter(unsigned long long *pull; unsigned long long value);

lemma void create_counter(unsigned long long *pull);
    requires *pull |-> 0;
    ensures counter(pull, 0);

lemma void destroy_counter(unsigned long long *pull);
    requires counter(pull, ?value);
    ensures *pull |-> value;

@*/

unsigned long long get_counter_plus_one(unsigned long long *pull);
//@ requires [?f]counter(pull, ?value);
//@ ensures [f]counter(pull, value) &*& result == value + 1;
//@ terminates;
// { return *pull + 1; }

/*@

typedef lemma void atomic_load_counter_op(unsigned long long *object, predicate() P, predicate(int) Q)();
    requires [?f]counter(object, ?value) &*& P();
    ensures [f]counter(object, value) &*& Q(value);

typedef lemma void atomic_load_counter_ghost_op(unsigned long long *object, predicate() pre, predicate(int) post, int callerThread)();
    requires is_atomic_load_counter_op(?op, object, ?P, ?Q) &*& P() &*& pre() &*& currentThread == callerThread &*& atomic_spaces({});
    ensures is_atomic_load_counter_op(op, object, P, Q) &*& Q(?value) &*& post(value) &*& atomic_spaces({});

@*/

unsigned long long atomic_load_counter(unsigned long long *object);
    /*@
    requires
        is_atomic_load_counter_ghost_op(?ghop, object, ?pre, ?post, currentThread) &*& pre();
    @*/
    //@ ensures post(result);
    //@ terminates;

/*@

typedef lemma void atomic_store_counter_op(unsigned long long *object, unsigned long long desired, predicate() P, predicate() Q)();
    requires counter(object, ?oldValue) &*& P() &*& desired <= oldValue + 1;
    ensures counter(object, desired) &*& Q();

typedef lemma void atomic_store_counter_ghost_op(unsigned long long *object, unsigned long long desired, predicate() pre, predicate() post, int callerThread)();
    requires is_atomic_store_counter_op(?op, object, desired, ?P, ?Q) &*& P() &*& pre() &*& currentThread == callerThread &*& atomic_spaces({});
    ensures is_atomic_store_counter_op(op, object, desired, P, Q) &*& Q() &*& post() &*& atomic_spaces({});

@*/

void atomic_store_counter(unsigned long long *object, unsigned long long desired);
    /*@
    requires
        is_atomic_store_counter_ghost_op(?ghop, object, desired, ?pre, ?post, currentThread) &*& pre();
    @*/
    //@ ensures post();
    //@ terminates;

/*@

typedef lemma void atomic_fetch_and_increment_counter_op
    (unsigned long long *object, predicate() P, predicate(int) Q)();
    requires counter(object, ?old) &*& P();
    ensures counter(object, old + 1) &*& Q(old);

typedef lemma void atomic_fetch_and_increment_counter_ghost_op(unsigned long long *object, predicate() pre, predicate(int) post, int callerThread)();
    requires
        is_atomic_fetch_and_increment_counter_op(?op, object, ?P, ?Q) &*&
        P() &*& pre() &*& callerThread == currentThread &*&
        atomic_spaces({});
    ensures
        Q(?result) &*& post(result) &*&
        atomic_spaces({});
 
@*/

unsigned long long atomic_fetch_and_increment_counter(unsigned long long *object);
    /*@
    requires
        is_atomic_fetch_and_increment_counter_ghost_op(?ghop, object, ?pre, ?post, currentThread) &*&
        pre();
    @*/
    //@ ensures post(result);
    //@ terminates;

/*@

typedef lemma void atomic_increment_counter_op
    (unsigned long long *object, predicate() P, predicate() Q)();
    requires counter(object, ?old) &*& P();
    ensures counter(object, old + 1) &*& Q();

typedef lemma void atomic_increment_counter_ghost_op(unsigned long long *object, predicate() pre, predicate() post, int callerThread)();
    requires
        is_atomic_increment_counter_op(?op, object, ?P, ?Q) &*&
        P() &*& pre() &*& callerThread == currentThread &*&
        atomic_spaces({});
    ensures
        Q() &*& post() &*&
        atomic_spaces({});
 
@*/

void atomic_increment_counter(unsigned long long *object);
    /*@
    requires
        is_atomic_increment_counter_ghost_op(?ghop, object, ?pre, ?post, currentThread) &*&
        pre();
    @*/
    //@ ensures post();
    //@ terminates;

/*@

typedef lemma void atomic_decrement_counter_op
    (unsigned long long *object, predicate() P, predicate() Q)();
    requires counter(object, ?old) &*& P() &*& 1 <= old;
    ensures counter(object, old - 1) &*& Q();

typedef lemma void atomic_decrement_counter_ghost_op(unsigned long long *object, predicate() pre, predicate() post, int callerThread)();
    requires
        is_atomic_decrement_counter_op(?op, object, ?P, ?Q) &*&
        P() &*& pre() &*& callerThread == currentThread &*&
        atomic_spaces({});
    ensures
        Q() &*& post() &*&
        atomic_spaces({});
 
@*/

void atomic_decrement_counter(unsigned long long *object);
    /*@
    requires
        is_atomic_decrement_counter_ghost_op(?ghop, object, ?pre, ?post, currentThread) &*&
        pre();
    @*/
    //@ ensures post();
    //@ terminates;

#endif
