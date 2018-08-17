#ifndef STDATOMIC_H
#define STDATOMIC_H

/*@

predicate atomic_space(predicate() inv;);

lemma void create_atomic_space(predicate() inv);
    requires inv();
    ensures atomic_space(inv);

lemma void destroy_atomic_space();
    requires atomic_space(?inv);
    ensures inv();

@*/

/*@

typedef lemma void atomic_load_int_op(int *object, predicate() P, predicate(int) Q)();
    requires [?frac]*object |-> ?value &*& P();
    ensures [frac]*object |-> value &*& Q(value);

typedef lemma void atomic_load_int_ghost_op(predicate() inv, int *object, predicate() pre, predicate(int) post)();
    requires inv() &*& is_atomic_load_int_op(?op, object, ?P, ?Q) &*& P() &*& pre();
    ensures inv() &*& is_atomic_load_int_op(op, object, P, Q) &*& Q(?value) &*& post(value);

@*/

int atomic_load_int(int *object);
    /*@
    requires
        [?frac]atomic_space(?inv) &*&
        is_atomic_load_int_ghost_op(?ghop, inv, object, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        [frac]atomic_space(inv) &*&
        is_atomic_load_int_ghost_op(ghop, inv, object, pre, post) &*& post(result);
    @*/

/*@

typedef lemma void atomic_store_int_op(int *object, int desired, predicate() P, predicate() Q)();
    requires *object |-> _ &*& P();
    ensures *object |-> desired &*& Q();

typedef lemma void atomic_store_int_ghost_op(predicate() inv, int *object, int desired, predicate() pre, predicate() post)();
    requires inv() &*& is_atomic_store_int_op(?op, object, desired, ?P, ?Q) &*& P() &*& pre();
    ensures inv() &*& is_atomic_store_int_op(op, object, desired, P, Q) &*& Q() &*& post();

@*/

void atomic_store_int(int *object, int desired);
    /*@
    requires
        [?frac]atomic_space(?inv) &*&
        is_atomic_store_int_ghost_op(?ghop, inv, object, desired, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        [frac]atomic_space(inv) &*&
        is_atomic_store_int_ghost_op(ghop, inv, object, desired, pre, post) &*& post();
    @*/

/*@

typedef lemma void atomic_exchange_pointer_op
    (void **object, void *desired, predicate() P, predicate(void *) Q)();
    requires *object |-> ?old &*& P();
    ensures *object |-> desired &*& Q(old);

typedef lemma void atomic_exchange_pointer_ghost_op
    (predicate() inv, void **object, void *desired,
     predicate() pre, predicate(void *) post)();
    requires
        inv() &*&
        is_atomic_exchange_pointer_op(?op, object, desired, ?P, ?Q) &*&
        P() &*& pre();
    ensures
        inv() &*&
        is_atomic_exchange_pointer_op(op, object, desired, P, Q) &*&
        Q(?old) &*& post(old);

@*/

void *atomic_exchange_pointer(void **object, void *desired);
    /*@
    requires
        [?frac]atomic_space(?inv) &*&
        is_atomic_exchange_pointer_ghost_op(?ghop, inv, object, desired, ?pre, ?post)
        &*& pre();
    @*/
    /*@
    ensures
        [frac]atomic_space(inv) &*&
        is_atomic_exchange_pointer_ghost_op(ghop, inv, object, desired, pre, post)
        &*& post(result);
    @*/

#endif
