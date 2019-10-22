#ifndef ATOMICS_H
#define ATOMICS_H

/*@

predicate atomic_space(predicate() inv);

lemma void create_atomic_space(predicate() inv);
    requires inv();
    ensures atomic_space(inv);

lemma void dispose_atomic_space();
    requires atomic_space(?inv);
    ensures inv();

@*/

typedef long long prophecy_id;

//@ predicate prophecy(prophecy_id id, int value);

prophecy_id create_prophecy();
    //@ requires true;
    //@ ensures prophecy(result, _);

/*@

typedef lemma void atomic_load_int_op(int *object, int value, predicate() P, predicate() Q)();
    requires *object |-> ?value1 &*& P();
    ensures *object |-> value1 &*& value1 == value &*& Q();

typedef lemma void atomic_load_int_ghop(predicate() inv, int *object, int value, predicate() pre, predicate() post)();
    requires inv() &*& is_atomic_load_int_op(?op, object, value, ?P, ?Q) &*& P() &*& pre();
    ensures inv() &*& is_atomic_load_int_op(op, object, value, P, Q) &*& Q() &*& post();

@*/

int atomic_load_int(prophecy_id prophecy, int *object);
    /*@
    requires
        prophecy(prophecy, ?value) &*&
        [?f]atomic_space(?inv) &*&
        is_atomic_load_int_ghop(?ghop, inv, object, value, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_load_int_ghop(ghop, inv, object, value, pre, post) &*& post() &*& result == value;
    @*/

/*@

typedef lemma void atomic_increment_int_op(int *object, predicate() P, predicate() Q)();
    requires *object |-> ?value &*& P();
    ensures *object |-> value + 1 &*& Q();

typedef lemma void atomic_increment_int_ghop(predicate() inv, int *object, predicate() pre, predicate() post)();
    requires inv() &*& is_atomic_increment_int_op(?op, object, ?P, ?Q) &*& P() &*& pre();
    ensures inv() &*& is_atomic_increment_int_op(op, object, P, Q) &*& Q() &*& post();

@*/

void atomic_increment_int(int *object);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_atomic_increment_int_ghop(?ghop, inv, object, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_increment_int_ghop(ghop, inv, object, pre, post) &*& post();
    @*/

#endif
