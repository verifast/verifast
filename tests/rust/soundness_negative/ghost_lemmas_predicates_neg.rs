// verifast_options{skip_specless_fns}

// Soundness tests for VeriFast ghost machinery: predicates, lemmas,
// ghost loops, and verification conditions.

/*@

// =========================================================================
// PREDICATES & POSITIVE LEMMAS
// =========================================================================

pred nonneg_ghost(n: i32) = if n == 0 { true } else { 0 < n &*& nonneg_ghost(n - 1) };

pred token(id: i32, val: i32) = 0 <= id &*& val > 0;

lem valid_lemma_open_close(id: i32, val: i32)
    req token(id, val);
    ens token(id, val) &*& val > 0;
{
    open token(id, val);
    close token(id, val);
}

lem valid_lemma_induction(n: i32)
    req 0 <= n;
    ens nonneg_ghost(n);
{
    close nonneg_ghost(0);
    let i = 0;
    while i < n
        inv 0 <= i &*& i <= n &*& nonneg_ghost(i);
        decreases n - i;
    {
        i = i + 1;
        close nonneg_ghost(i);
    }
}

lem valid_helper(x: i32)
    req x > 5;
    ens x > 0;
{}

lem valid_helper_caller(x: i32)
    req x > 10;
    ens x > 5;
{
    valid_helper(x);
}

// =========================================================================
// NEGATIVE CASES: 12 should_fail cases
// =========================================================================

// 1. Opening a predicate that is not held in the symbolic heap
lem neg_open_unheld()
    req true;
    ens true;
{
    open token(1, 10); //~should_fail
}

// 2. Closing a predicate without satisfying its body condition (val > 0 is violated)
lem neg_close_unproven()
    req true;
    ens token(1, -5);
{
    close token(1, -5); //~should_fail
}

// 3. Calling a lemma whose precondition is not satisfied
lem lemma_req_positive(x: i32)
    req x > 10;
    ens x > 5;
{}

lem neg_call_bad_pre()
    req true;
    ens true;
{
    lemma_req_positive(3); //~should_fail
}

// 4. Non-terminating recursive lemma without a decrease measure
lem neg_rec_no_decrease(n: i32)
    req n >= 0;
    ens true;
{
    if n > 0 {
        neg_rec_no_decrease(n - 1); //~should_fail
    }
}

// 5. Division by zero in ghost assertion
lem neg_ghost_div_zero()
    req true;
    ens true;
{
    assert 10 / 0 == 1; //~should_fail
}

// 6. Arithmetic contradiction in ghost assertion
lem neg_ghost_false_ineq()
    req true;
    ens true;
{
    assert 5 > 10; //~should_fail
}

// 7. Asserting false in ghost code
lem neg_ghost_assert_false()
    req true;
    ens true;
{
    assert false; //~should_fail
}

// 8. Lemma failing to establish its declared postcondition
lem neg_ghost_missing_post()
    req true;
    ens false; //~should_fail
{
}

// 9. Opening a predicate with wrong index/argument
lem neg_open_wrong_arg(id1: i32, id2: i32, val: i32)
    req token(id1, val) &*& id1 != id2;
    ens true;
{
    open token(id2, val); //~should_fail
}

// 10. Consuming a predicate twice when only one chunk is held
lem neg_double_consume_pred(id: i32, val: i32)
    req token(id, val);
    ens token(id, val) &*& token(id, val); //~should_fail
{
}

// 11. Ghost loop invariant not preserved across iterations
lem neg_loop_inv_not_preserved(n: i32)
    req n > 0;
    ens true;
{
    let i = 0;
    while i < n
        inv i == 0; //~should_fail
        decreases n - i;
    {
        i = i + 1;
    }
}

// 12. Ghost loop decrease measure not decreasing
lem neg_loop_decrease_not_decreasing(n: i32)
    req n > 0;
    ens true;
{
    let i = 0;
    while i < n
        inv 0 <= i &*& i <= n;
        decreases n; //~should_fail
    {
        i = i + 1;
    }
}

@*/

fn main() {}
