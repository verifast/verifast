#include <stdint.h>

/*@

lemma void mul_mono_l(int a1, int a2, int b)
    requires a1 <= a2 &*& 0 <= b;
    ensures a1 * b <= a2 * b;
{
    for (int i = 0; i < b; i++)
        invariant i <= b &*& a1 * i <= a2 * i;
        decreases b - i;
    {}
}

lemma void mul_mono_r(int a, int b1, int b2)
    requires 0 <= a &*& b1 <= b2;
    ensures a * b1 <= a * b2;
{
    for (int i = 0; i < a; i++)
        invariant i <= a &*& i * b1 <= i * b2;
        decreases a - i;
    {}
}

fixpoint int mul(int x, int y);

lemma void mul_def(int x, int y);
    requires true;
    ensures mul(x, y) == x * y;

@*/

long long foo(long long x, int64_t y)
    //@ requires 0 <= x &*& 0 < y &*& x <= LLONG_MAX - y;
    //@ ensures result == x + y;  //~ should_fail
{
    assert(LLONG_MAX == 0x7fffffffffffffff);
    assert(LLONG_MIN == -0x7fffffffffffffff - 1);
    long long z = 8001002003004005006;
    z = -8001002003004005006;
    z = x + y;
    z = x - y;
    if (x <= LLONG_MAX / y) {
        //@ div_rem(LLONG_MAX, y);
        //@ mul_def(LLONG_MAX / y, y);
        //@ assert mul(LLONG_MAX / y, y) + LLONG_MAX % y == LLONG_MAX;
        //@ if (LLONG_MAX / y < 0) {} else {}
        //@ if (LLONG_MAX % y < 0) {} else {}
        //@ mul_mono_r(x, 1, y);
        //@ mul_mono_l(x, LLONG_MAX / y, y);
        //@ mul_def(LLONG_MAX / y, y);
        //@ assert LLONG_MAX / y * y + LLONG_MAX % y == LLONG_MAX;
        z = x * y;
    }
    z = x / y;
    z = x & y;
    z = x | y;
    z = x ^ y;
    return x - y;
}

unsigned long long bar(unsigned long long x, uint64_t y)
    //@ requires 0 <= x &*& 100200300400500 <= x &*& y <= x &*& y != 0 &*& x + y <= ULLONG_MAX;
    //@ ensures result == x + y;  //~ should_fail
{
    unsigned long long z = 16001002003004005006U;
    z = x + y;
    z = x - y;
    if (x <= ULLONG_MAX / y) {
        //@ div_rem(ULLONG_MAX, y);
        //@ mul_def(ULLONG_MAX / y, y);
        //@ assert mul(ULLONG_MAX / y, y) + ULLONG_MAX % y == ULLONG_MAX;
        //@ if (ULLONG_MAX / y < 0) {} else {}
        //@ if (ULLONG_MAX % y < 0) {} else {}
        //@ mul_mono_r(x, 1, y);
        //@ mul_mono_l(x, ULLONG_MAX / y, y);
        //@ mul_def(ULLONG_MAX / y, y);
        //@ assert ULLONG_MAX / y * y + ULLONG_MAX % y == ULLONG_MAX;
        z = x * y;
    }
    z = x / y;
    z = x & y;
    z = x | y;
    z = x ^ y;
    return x - y;
}
