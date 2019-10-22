#ifndef SPLITCOUNTER_H
#define SPLITCOUNTER_H

struct counter;

//@ predicate counter(struct counter *counter, predicate(int) inv);

struct counter *create_counter();
    //@ requires exists<predicate(int)>(?inv) &*& inv(0);
    //@ ensures counter(result, inv);

void dispose_counter(struct counter *c);
    //@ requires counter(c, ?inv);
    //@ ensures inv(_);

/*@

typedef lemma void incr_ghop(predicate(int) inv, predicate() pre, predicate() post)();
    requires inv(?value) &*& pre();
    ensures inv(value + 1) &*& post();

@*/

void incr_left(struct counter *counter);
    //@ requires [?f]counter(counter, ?inv) &*& is_incr_ghop(?ghop, inv, ?pre, ?post) &*& pre();
    //@ ensures [f]counter(counter, inv) &*& is_incr_ghop(ghop, inv, pre, post) &*& post();

void incr_right(struct counter *counter);
    //@ requires [?f]counter(counter, ?inv) &*& is_incr_ghop(?ghop, inv, ?pre, ?post) &*& pre();
    //@ ensures [f]counter(counter, inv) &*& is_incr_ghop(ghop, inv, pre, post) &*& post();

/*@

typedef lemma void read_ghop(predicate(int) inv, predicate() pre, predicate(int) post)();
    requires inv(?value) &*& pre();
    ensures inv(value) &*& post(value);

@*/

long long read(struct counter *counter);
    //@ requires [?f]counter(counter, ?inv) &*& is_read_ghop(?ghop, inv, ?pre, ?post) &*& pre();
    //@ ensures [f]counter(counter, inv) &*& post(result);

#endif
