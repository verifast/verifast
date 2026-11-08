#include "limits.h"

/* ========================================================================== */
/* Positive Verified Arithmetic & Shift Functions                             */
/* ========================================================================== */

int safe_add(int a, int b)
//@ requires 0 <= a && a <= 1000 &*& 0 <= b && b <= 1000;
//@ ensures result == a + b &*& 0 <= result && result <= 2000;
{
    return a + b;
}

int safe_sub(int a, int b)
//@ requires 0 <= a && a <= 1000 &*& 0 <= b && b <= 1000;
//@ ensures result == a - b &*& -1000 <= result && result <= 1000;
{
    return a - b;
}

int safe_mul(int a, int b)
//@ requires 0 <= a && a <= 100 &*& 0 <= b && b <= 100 &*& 0 <= a * b && a * b <= INT_MAX;
//@ ensures result == a * b;
{
    return a * b;
}

int safe_div(int nom, int denom)
//@ requires denom != 0 &*& !(nom == INT_MIN && denom == -1);
//@ ensures result == nom / denom;
{
    return nom / denom;
}

int safe_mod(int nom, int denom)
//@ requires denom != 0 &*& !(nom == INT_MIN && denom == -1);
//@ ensures result == nom % denom;
{
    return nom % denom;
}

int safe_shift_left(int x, int shift)
//@ requires 0 <= x && 0 <= shift &*& shift < ((8 * sizeof(int)) - 1) &*& 0 <= (x << shift) && (x << shift) <= INT_MAX;
//@ ensures result == (x << shift);
{
    return x << shift;
}

int safe_shift_right(int x, int shift)
//@ requires 0 <= x && 0 <= shift &*& shift < ((8 * sizeof(int)) - 1);
//@ ensures result == (x >> shift);
{
    return x >> shift;
}

short safe_narrowing(int x)
//@ requires -30000 <= x && x <= 30000;
//@ ensures result == x;
{
    return (short)x;
}

/* ========================================================================== */
/* Negative Soundness Tests (20 Should-Fail Cases)                            */
/* ========================================================================== */

/* 1. Signed integer addition overflow (constant INT_MAX + 1) */
int neg_add_overflow_const(int x)
//@ requires x == INT_MAX;
//@ ensures true;
{
    return x + 1; //~ should_fail
}

/* 2. Signed integer addition overflow (symbolic inputs) */
int neg_add_overflow_sym(int x, int y)
//@ requires x == INT_MAX && y == 1;
//@ ensures true;
{
    return x + y; //~ should_fail
}

/* 3. Signed integer subtraction underflow (constant INT_MIN - 1) */
int neg_sub_underflow_const(int x)
//@ requires x == INT_MIN;
//@ ensures true;
{
    return x - 1; //~ should_fail
}

/* 4. Signed integer subtraction underflow (symbolic inputs) */
int neg_sub_underflow_sym(int x, int y)
//@ requires x == INT_MIN && y == 1;
//@ ensures true;
{
    return x - y; //~ should_fail
}

/* 5. Signed integer negation overflow (-INT_MIN) */
int neg_negation_overflow(int x)
//@ requires x == INT_MIN;
//@ ensures true;
{
    return -x; //~ should_fail
}

/* 6. Signed integer multiplication overflow (INT_MAX * 2) */
int neg_mul_overflow_positive(int x)
//@ requires x == INT_MAX;
//@ ensures true;
{
    return x * 2; //~ should_fail
}

/* 7. Signed integer multiplication overflow negative (INT_MIN * -1) */
int neg_mul_overflow_negative(int x)
//@ requires x == INT_MIN;
//@ ensures true;
{
    return x * -1; //~ should_fail
}

/* 8. Signed division overflow (INT_MIN / -1) */
int neg_div_overflow(int x, int y)
//@ requires x == INT_MIN && y == -1;
//@ ensures true;
{
    return x / y; //~ should_fail
}

/* 9. Signed modulo overflow (INT_MIN % -1) */
int neg_mod_overflow(int x, int y)
//@ requires x == INT_MIN && y == -1;
//@ ensures true;
{
    return x % y; //~ should_fail
}

/* 10. Division by constant zero */
int neg_div_const_zero(int x)
//@ requires true;
//@ ensures true;
{
    return x / 0; //~ should_fail
}

/* 11. Modulo by constant zero */
int neg_mod_const_zero(int x)
//@ requires true;
//@ ensures true;
{
    return x % 0; //~ should_fail
}

/* 12. Division by symbolic zero */
int neg_div_sym_zero(int x, int y)
//@ requires y == 0;
//@ ensures true;
{
    return x / y; //~ should_fail
}

/* 13. Left-shift by negative amount */
int neg_shift_left_negative_amount(int x)
//@ requires 0 <= x && x <= 100;
//@ ensures true;
{
    return x << -1; //~ should_fail
}

/* 14. Right-shift by negative amount */
int neg_shift_right_negative_amount(int x)
//@ requires 0 <= x && x <= 100;
//@ ensures true;
{
    return x >> -1; //~ should_fail
}

/* 15. Left-shift by >= 32 bits (undefined behavior in C) */
int neg_shift_left_excessive(int x)
//@ requires 0 <= x && x <= 100;
//@ ensures true;
{
    return x << 32; //~ should_fail
}

/* 16. Right-shift by >= 32 bits */
int neg_shift_right_excessive(int x)
//@ requires 0 <= x && x <= 100;
//@ ensures true;
{
    return x >> 32; //~ should_fail
}

/* 17. Left-shift of negative signed integer */
int neg_shift_left_negative_value(int x)
//@ requires x == -1;
//@ ensures true;
{
    return x << 1; //~ should_fail
}

/* 18. Right-shift of negative signed integer */
int neg_shift_right_negative_value(int x)
//@ requires x == -1;
//@ ensures true;
{
    return x >> 1; //~ should_fail
}

/* 19. Narrowing cast overflow (int value exceeding short range) */
short neg_narrowing_overflow(int x)
//@ requires x == 100000;
//@ ensures true;
{
    return (short)x; //~ should_fail
}

/* 20. Truncating cast postcondition mismatch */
short neg_truncating_mismatch(int x)
//@ requires x == 100000;
//@ ensures result == x; //~ should_fail
{
    short s = /*@ truncating @*/ (short)x;
    return s;
}
