#include "stdlib.h"

/* ========================================================================== */
/* Positive Verified Predicates, Fixpoints, and Lemmas                        */
/* ========================================================================== */

/*@
predicate valid_bounded_int(int *p; int val) =
    integer(p, val) &*& 0 <= val &*& val <= 1000;

fixpoint int list_sum(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(h, t): return h + list_sum(t);
    }
}

lemma void list_sum_append(list<int> xs, list<int> ys)
    requires true;
    ensures list_sum(append(xs, ys)) == list_sum(xs) + list_sum(ys);
{
    switch (xs) {
        case nil:
        case cons(h, t):
            list_sum_append(t, ys);
    }
}

lemma void valid_bounded_is_nonneg(int *p)
    requires valid_bounded_int(p, ?v);
    ensures valid_bounded_int(p, v) &*& 0 <= v;
{
    open valid_bounded_int(p, v);
    close valid_bounded_int(p, v);
}
@*/

void safe_predicate_open_close(int *p)
//@ requires valid_bounded_int(p, ?v) &*& v < 1000;
//@ ensures valid_bounded_int(p, v + 1);
{
    //@ open valid_bounded_int(p, v);
    *p = *p + 1;
    //@ close valid_bounded_int(p, v + 1);
}

/* ========================================================================== */
/* Negative Soundness Tests (11 Should-Fail Cases)                            */
/* ========================================================================== */

/* 1. Opening a predicate without holding its chunk */
void neg_open_without_chunk(int *p)
//@ requires true;
//@ ensures true;
{
    //@ open valid_bounded_int(p, _); //~ should_fail
}

/* 2. Closing a predicate when its invariant is violated (v = -5 < 0) */
void neg_close_invariant_violation(int *p)
//@ requires integer(p, -5);
//@ ensures integer(p, -5);
{
    //@ close valid_bounded_int(p, -5); //~ should_fail
}

/* 3. Non-terminating recursive lemma without decrease */
/*@
lemma void neg_nonterminating_lemma(int n)
    requires true;
    ensures true;
{
    neg_nonterminating_lemma(n); //~ should_fail
}
@*/

/* 4. Mutual lemma recursion cycle without decrease */
/*@
lemma void neg_mutual_lemma_b(int n);
    requires true;
    ensures true;

lemma void neg_mutual_lemma_a(int n)
    requires true;
    ensures true;
{
    neg_mutual_lemma_b(n); //~ should_fail
}

lemma void neg_mutual_lemma_b(int n)
    requires true;
    ensures true;
{
    neg_mutual_lemma_a(n);
}
@*/

/* 5. Lemma recursion on non-structurally-smaller inductive argument */
/*@
lemma void neg_non_structural_lemma(list<int> xs)
    requires true;
    ensures true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            neg_non_structural_lemma(xs); //~ should_fail
    }
}
@*/

/* 6. Asserting false pure fact */
void neg_assert_false_fact()
//@ requires true;
//@ ensures true;
{
    //@ assert 1 == 2; //~ should_fail
}

/* 7. Consuming chunk not held in state */
void neg_consume_unheld_chunk(int *p)
//@ requires true;
//@ ensures true;
{
    //@ assert integer(p, _); //~ should_fail
}

/* 8. Calling lemma whose precondition fails */
/*@
lemma void lemma_requires_strictly_positive(int *p)
    requires valid_bounded_int(p, ?v) &*& v > 0;
    ensures valid_bounded_int(p, v);
{
    open valid_bounded_int(p, v);
    close valid_bounded_int(p, v);
}
@*/

void neg_call_lemma_precondition_failure(int *p)
//@ requires valid_bounded_int(p, 0);
//@ ensures valid_bounded_int(p, 0);
{
    //@ lemma_requires_strictly_positive(p); //~ should_fail
}

/* 9. Fabricating duplicate copy of linear chunk */
void neg_duplicate_linear_chunk(int *p)
//@ requires valid_bounded_int(p, ?v);
//@ ensures valid_bounded_int(p, v) &*& valid_bounded_int(p, v); //~ should_fail
{
}

/* 10. Leaking predicate chunk when postcondition requires emp */
void neg_leak_predicate_chunk(int *p)
//@ requires valid_bounded_int(p, 10);
//@ ensures emp;
{
} //~ should_fail

/* 11. Loop in lemma with failing / non-decreasing variant */
/*@
lemma void neg_lemma_bad_decreases(int n)
    requires 0 <= n;
    ensures true;
{
    for (int i = 0; i < n; i++)
        invariant 0 <= i &*& i <= n;
        decreases i; //~ should_fail
    {
    }
}
@*/
