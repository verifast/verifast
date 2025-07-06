/*@

predicate atomic_space(predicate() inv);
predicate opened_atomic_spaces(list<predicate()> openedSpaces);

lemma void create_atomic_space(predicate() inv);
    requires inv();
    ensures [_]atomic_space(inv);

lemma void open_atomic_space(predicate() inv);
    requires opened_atomic_spaces(?spaces) &*& [_]atomic_space(inv) &*& !mem(inv, spaces);
    ensures opened_atomic_spaces(cons(inv, spaces)) &*& inv();

lemma void close_atomic_space(predicate() inv);
    requires opened_atomic_spaces(?spaces) &*& inv();
    ensures opened_atomic_spaces(remove(inv, spaces));

@*/



// -----------------------------------------------------------------------



/*@

predicate do_atomic_fetch_and_negate_pre(int *x);
predicate do_atomic_fetch_and_negate_post(int result);

lemma int do_atomic_fetch_and_negate(int *x);
    requires *x |-> ?v &*& do_atomic_fetch_and_negate_pre(x);
    ensures *x |-> -v &*& do_atomic_fetch_and_negate_post(v) &*& result == v;

typedef lemma void atomic_fetch_and_negate_safety_proof(int *x, predicate() pre, predicate(int) post)();
    requires opened_atomic_spaces({}) &*& do_atomic_fetch_and_negate_pre(x) &*& pre();
    ensures opened_atomic_spaces({}) &*& do_atomic_fetch_and_negate_post(?result) &*& post(result);

@*/

int atomic_fetch_and_negate(int *x);
//@ requires is_atomic_fetch_and_negate_safety_proof(?proof, x, ?pre, ?post) &*& pre();
//@ ensures post(result);



// -----------------------------------------------------------------------



typedef void forkee/*@(predicate() pre)@*/();
//@ requires pre();
//@ ensures true;

void fork(forkee *forkee);
//@ requires [_]is_forkee(forkee, ?pre) &*& pre();
//@ ensures true;
