/*@

lemma void truncate_int32_def(int x);
    requires 0 <= x;
    ensures x == ((x >> 32) << 32) + (truncating (unsigned)x);

@*/

void test(long x)
    //@ requires true;
    //@ ensures true;
{
    unsigned a = 0x10203040;
    unsigned b = /*@truncating@*/(a << 16);
    
    unsigned long long al = a;
    unsigned long long bl = al << 16;
    
    assert(b == /*@truncating@*/(unsigned)bl);
    //@ truncate_int32_def(bl);
    //@ produce_limits(b);
    //@ if (bl >> 32 < 0x1020) {} else if (bl >> 32 > 0x1020) {} else {}
    assert(b == 0x30400000);
}
