#include "stdlib.h"

/* ========================================================================== */
/* Positive Verified Fractional Permission & Concurrency Functions           */
/* ========================================================================== */

int safe_fractional_read(int *p)
//@ requires [1/2]integer(p, ?v);
//@ ensures [1/2]integer(p, v) &*& result == v;
{
    return *p;
}

void safe_fraction_split_merge(int *p)
//@ requires integer(p, ?v);
//@ ensures integer(p, v);
{
    //@ assert [1/2]integer(p, v);
    int r1 = safe_fractional_read(p);
    int r2 = safe_fractional_read(p);
    //@ assert r1 == r2;
}

void safe_fraction_write_after_merge(int *p, int new_val)
//@ requires [1/2]integer(p, ?v1) &*& [1/2]integer(p, ?v2);
//@ ensures integer(p, new_val);
{
    *p = new_val;
}

typedef int (* binary_math_op)(int a, int b);
    //@ requires 0 <= a && a <= 1000 &*& 0 <= b && b <= 1000;
    //@ ensures result == a + b;

int safe_add_impl(int a, int b)
//@ requires 0 <= a && a <= 1000 &*& 0 <= b && b <= 1000;
//@ ensures result == a + b;
{
    return a + b;
}

int safe_call_funcptr(binary_math_op op, int a, int b)
//@ requires is_binary_math_op(op) == true &*& 0 <= a && a <= 1000 &*& 0 <= b && b <= 1000;
//@ ensures result == a + b;
{
    return op(a, b);
}

struct Cell {
    int val;
};

int safe_fractional_struct_read(struct Cell *c)
//@ requires [1/2]c->val |-> ?v;
//@ ensures [1/2]c->val |-> v &*& result == v;
{
    return c->val;
}

/* ========================================================================== */
/* Negative Soundness Tests (10 Should-Fail Cases)                            */
/* ========================================================================== */

/* 1. Writing through a fractional (read-only) permission */
void neg_write_fractional(int *p)
//@ requires [1/2]integer(p, 10);
//@ ensures [1/2]integer(p, _);
{
    *p = 42; //~ should_fail
}

/* 2. Consuming full permission [1] when only [1/2] is available */
void helper_need_full_permission(int *p)
//@ requires integer(p, ?v);
//@ ensures integer(p, v);
{
}

void neg_consume_full_with_half(int *p)
//@ requires [1/2]integer(p, 10);
//@ ensures [1/2]integer(p, 10);
{
    helper_need_full_permission(p); //~ should_fail
}

/* 3. Freeing pointer when only fractional heap block permission is held */
void neg_free_fractional_pointer(int *p)
//@ requires [1/2]integer(p, ?v) &*& [1/2]malloc_block_ints(p, 1);
//@ ensures true;
{
    free(p); //~ should_fail
}

/* 4. Requesting zero fraction [0] */
void neg_request_zero_fraction(int *p)
//@ requires [1/2]integer(p, 10);
//@ ensures true;
{
    //@ assert [0]integer(p, 10); //~ should_fail
}

/* 5. Requesting fraction greater than held (e.g. [3/4] from [1/2]) */
void neg_request_excess_fraction(int *p)
//@ requires [1/2]integer(p, 10);
//@ ensures true;
{
    //@ assert [3/4]integer(p, 10); //~ should_fail
}

/* 6. Calling function pointer without holding is_funcptr permission */
int neg_call_funcptr_without_spec(binary_math_op op, int a, int b)
//@ requires 0 <= a && a <= 1000 &*& 0 <= b && b <= 1000;
//@ ensures true;
{
    return op(a, b); //~ should_fail
}

/* 7. Calling function pointer with violated precondition */
int neg_call_funcptr_precond_violation(binary_math_op op)
//@ requires is_binary_math_op(op) == true;
//@ ensures true;
{
    return op(-5, 10); //~ should_fail
}

/* 8. Asserting wrong fractional value for memory location */
void neg_assert_wrong_fractional_value(int *p)
//@ requires [1/2]integer(p, 10);
//@ ensures [1/2]integer(p, 10);
{
    //@ assert [1/2]integer(p, 20); //~ should_fail
}

/* 9. Writing through fractional struct field */
void neg_write_fractional_struct_field(struct Cell *c)
//@ requires [1/3]c->val |-> 5;
//@ ensures [1/3]c->val |-> _;
{
    c->val = 99; //~ should_fail
}

/* 10. Leaking fractional chunk when postcondition requires emp */
void neg_leak_fractional_chunk(int *p)
//@ requires [1/4]integer(p, 42);
//@ ensures emp;
{
} //~ should_fail
