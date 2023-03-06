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

typedef lemma void atomic_store_int_op(int *object, int desired, predicate() P, predicate() Q)();
    requires *object |-> _ &*& P();
    ensures *object |-> desired &*& Q();

typedef lemma void atomic_store_int_ghost_op(predicate() inv, int *object, int desired, predicate() pre, predicate() post, int callerThread)();
    requires inv() &*& is_atomic_store_int_op(?op, object, desired, ?P, ?Q) &*& P() &*& pre() &*& currentThread == callerThread;
    ensures inv() &*& is_atomic_store_int_op(op, object, desired, P, Q) &*& Q() &*& post();

@*/

void atomic_store_int(int *object, int desired);
    /*@
    requires
        [?frac]atomic_space(?inv) &*&
        is_atomic_store_int_ghost_op(?ghop, inv, object, desired, ?pre, ?post, currentThread) &*& pre();
    @*/
    /*@
    ensures
        [frac]atomic_space(inv) &*&
        is_atomic_store_int_ghost_op(ghop, inv, object, desired, pre, post, currentThread) &*& post();
    @*/
    //@ terminates;

/*@

typedef lemma void compare_and_swap_int_op
    (int *object, int oldValue, int newValue, predicate() P, predicate(int) Q)();
    requires *object |-> ?old &*& P();
    ensures *object |-> (old == oldValue ? newValue : old) &*& Q(old);

typedef lemma void compare_and_swap_int_ghost_op
    (predicate() inv, int *object, int oldValue, int newValue,
     predicate() pre, predicate(int) post)();
    requires
        inv() &*&
        is_compare_and_swap_int_op(?op, object, oldValue, newValue, ?P, ?Q) &*&
        P() &*& pre();
    ensures
        inv() &*&
        is_compare_and_swap_int_op(op, object, oldValue, newValue, P, Q) &*&
        Q(?result) &*& post(result);
 
@*/

int compare_and_swap_int(int *object, int oldValue, int newValue);
    /*@
    requires
        [?frac]atomic_space(?inv) &*&
        is_compare_and_swap_int_ghost_op(?ghop, inv, object, oldValue, newValue, ?pre, ?post) &*&
        pre();
    @*/
    /*@
    ensures
        [frac]atomic_space(inv) &*&
        post(result);
    @*/
    //@ terminates;

#endif
