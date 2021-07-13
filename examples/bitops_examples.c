//@ #include <bitops.gh>
//@ #include <target.gh>
#include <stdint.h>
#include <assert.h>

/*@

lemma void test()
    requires true;
    ensures 0 == (0x01 & 0x10);
{
    bitand_def(0x01, Zdigit(Zsign(false), true), 0x10, Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zsign(false), true), false), false), false), false));
}

lemma void Z_of_uint8_eq(Z z1, Z z2)
    requires z1 == Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zsign(false), ?b7), ?b6), ?b5), ?b4), ?b3), ?b2), ?b1), ?b0) &*& z2 == Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zsign(false), b7), b6), b5), b4), b3), b2), b1), b0);
    ensures z1 == z2;
{
}

lemma void bitand_uint8_symm(int x, int y)
    requires 0 <= x &*& x <= 255 &*& 0 <= y &*& y <= 255;
    ensures (x & y) == (y & x);
{
    Z zx = Z_of_uint8(x);
    Z zy = Z_of_uint8(y);
    bitand_def(x, zx, y, zy);
    bitand_def(y, zy, x, zx);
    Z_of_uint8_eq(Z_and(zx, zy), Z_and(zy, zx));
}

lemma void limits_test(int x, int y)
    requires 0 <= x &*& x <= UINT_MAX &*& 0 <= y &*& y <= UINT_MAX;
    ensures 0 <= (x | y) &*& (x | y) <= UINT_MAX;
{
    case_split_sizeof_int();
    bitor_limits(x, y, nat_of_int(8*sizeof(unsigned int)));
}

lemma void limits_test_64(int x, int y)
    requires 0 <= x &*& x <= 0xffffffffffffffff &*& 0 <= y &*& y <= 0xffffffffffffffff;
    ensures 0 <= (x & y) &*& (x & y) <= 0xffffffffffffffff;
{
    bitand_limits(x, y, N64);
}

lemma void limits_test_24(int x, int y)
    requires 0 <= x &*& x <= 0xffffff &*& 0 <= y &*& y <= 0xffffff;
    ensures 0 <= (x ^ y) &*& (x ^ y) <= 0xffffff;
{
    assert int_of_nat(Ndec({N2, N4})) == 24;
    bitxor_limits(x, y, Ndec({N2, N4}));
}

lemma unsigned char truncate_unsigned_test(int x)
    requires x == 0x123;
    ensures result == 0x23;
{
    truncate_unsigned_def(0x123, N8);
    return truncating (unsigned char) x;
}

lemma unsigned char truncate_unsigned_negative_operand_test(int x)
    requires x == -1;
    ensures result == 0xff;
{
    truncate_unsigned_def(-1, N8);
    return truncating (unsigned char) x;
}

lemma signed char truncate_signed_test(int x)
    requires x == 0xff;
    ensures result == -1;
{
    Z z = Z_of_uint8(0xff);
    truncate_signed_def(0xff, z, N7);
    return truncating (signed char) x;
}

@*/

void bitand_uint8_symm_test(uint8_t x, uint8_t y)
//@ requires true;
//@ ensures true;
{
    //@ Z_of_uint8(x);
    //@ Z_of_uint8(y);
    assert((x & y) == (y & x));
    //@ Z_of_uint8(123);
    assert((x & 123) == (123 & x));
}
