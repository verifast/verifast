//@ #include <bitops.gh>

/*@

lemma void int_of_bits_of_int(int x, nat n)
    requires 0 <= x;
    ensures x == int_of_bits(fst(bits_of_int(x, n)), snd(bits_of_int(x, n)));
{
    switch (n) {
        case zero:
        case succ(n0):
            div_rem(x, 2);
            int_of_bits_of_int(x / 2, n0);
    }
}

lemma Z int_of_Z_of_uintN(int x, nat N)
    requires 0 <= x &*& x < pow_nat(2, N);
    ensures result == Z_of_uintN(x, N) &*& x == int_of_Z(result);
{
    switch (N) {
        case zero:
            Z_of_uintN_def(x, N);
            return Z_of_uintN(x, N);
        case succ(N0):
            div_rem(x, 2);
            Z_of_uintN_def(x / 2, N0);
            int_of_Z_of_uintN(x / 2, N0);
            int_of_bits_of_int(x, N);
            Z_of_uintN_def(x, N);
            return Z_of_uintN(x, N);
    }
}

lemma Z Z_of_uint8(int x)
    requires 0 <= x &*& x <= 255;
    ensures result == Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zsign(false), _), _), _), _), _), _), _), _) &*& result == Z_of_uintN(x, N8) &*& x == int_of_Z(result);
{
    Z_of_uintN_def(x, N8);
    return int_of_Z_of_uintN(x, N8);
}

lemma Z Z_of_uint16(int x)
    requires 0 <= x &*& x <= 65535;
    ensures result == Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zsign(false), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _) &*& result == Z_of_uintN(x, N16) &*& x == int_of_Z(result);
{
    Z_of_uintN_def(x, N16);
    return int_of_Z_of_uintN(x, N16);
}

lemma Z Z_of_uint32(int x)
    requires 0 <= x &*& x <= 0xffffffff;
    ensures result == Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zdigit(Zsign(false), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _), _) &*& result == Z_of_uintN(x, N32) &*& x == int_of_Z(result);
{
    Z_of_uintN_def(x, N32);
    return int_of_Z_of_uintN(x, N32);
}

@*/