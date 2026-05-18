// `x & 1` used to be equated with `x % 2`, which disagrees for negative odd x.

#include <assert.h>

void test(int x)
//@ requires x < 0;
//@ ensures true;
{
    int y = x & 1;
    int z = x % 2;
    assert(z >= 0); //~ should_fail
}
