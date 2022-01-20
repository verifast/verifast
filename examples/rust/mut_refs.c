//@ #include <listex.gh>
#include <stdio.h>

/*

fn max(a: &mut i32, b: &mut i32): &mut i32 {
  if (a < b)
    return b;
  else
    return a;
}

*/

//@ predicate int_object(int *px) = *px |-> _;

/*@

fixpoint bool bag_eq<t>(list<t> xs, list<t> ys) {
    return length(xs) == length(ys) && remove_all(xs, ys) == nil;
}

@*/

/*

A mutable reference translates to a points-to chunk.

The precondition specifies the points-to chunks for the arguments;
the postcondition specifies the points-to chunk for the result, plus
the pool of points-to chunks for the dropped mutable references.
The bag of incoming mutable references shall equal the bag of outgoing
mutable references. (We can equivalently say "set" here instead of "bag",
because due to the
points-to chunks, the objects are known to be distinct.)

*/

int *max(int *a, int *b)
//@ requires *a |-> _ &*& *b |-> _;
//@ ensures *result |-> _ &*& foreach(?xs, int_object) &*& bag_eq({a, b}, cons(result, xs)) == true;
{
    if (*a < *b) {
        //@ close int_object(a);
        //@ close foreach(nil, int_object);
        //@ close foreach({a}, int_object);
        return b;
    } else {
        //@ close int_object(b);
        //@ close foreach(nil, int_object);
        //@ close foreach({b}, int_object);
        return a;
    }
}

/*@

lemma void foreach_bag_eq<t>(list<t> xs, list<t> ys);
    requires foreach(xs, ?p) &*& bag_eq(ys, xs) == true;
    ensures foreach(ys, p);
// Proof: TODO

@*/

int main()
//@ requires true;
//@ ensures true;
{
    int x = 0;
    int y = 42;

    int *r = max(&x, &y);
    
    printf("%d\b", *r);

    //@ assert foreach(?xs, int_object);
    //@ close int_object(r);
    //@ close foreach(cons(r, xs), int_object);
    //@ foreach_bag_eq(cons(r, xs), {&x, &y});
    //@ open foreach({&x, &y}, int_object);
    //@ open int_object(&x);
    //@ open foreach({&y}, int_object);
    //@ open int_object(&y);
    //@ open foreach({}, int_object);

    return 0;
}
