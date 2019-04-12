#include <stdint.h>

/*@

lemma void truncate_int32_def(int x);
    requires 0 <= x;
    ensures x == ((x >> 32) << 32) + (truncating (uint32_t)x);

@*/

void test(long x)
    //@ requires true;
    //@ ensures true;
{
    uint32_t a = 0x10203040;
    uint32_t b = /*@truncating@*/(a << 16);
    
    uint64_t al = a;
    uint64_t bl = al << 16;
    
    assert(b == /*@truncating@*/(uint32_t)bl);
    //@ truncate_int32_def(bl);
    //@ produce_limits(b);
    //@ if (bl >> 32 < 0x1020) {} else if (bl >> 32 > 0x1020) {} else {}
    assert(b == 0x30400000UL);
}
