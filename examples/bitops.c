/*@

inductive Z = sign(bool) | digit(Z, bool);

fixpoint int int_of_Z(Z z) {
    switch (z) {
        case sign(b): return b ? -1 : 0;
        case digit(z0, b0): return 2 * int_of_Z(z0) + (b0 ? 1 : 0);
    }
}

fixpoint Z Z_and(Z z1, Z z2) {
    switch (z1) {
        case sign(b1): return b1 ? z2 : z1;
        case digit(z10, b10): return switch (z2) {
            case sign(b2): return b2 ? z1 : z2;
            case digit(z20, b20): return digit(Z_and(z10, z20), b10 && b20);
        };
    }
}

lemma void bitand_def(int x1, int x2, Z z1, Z z2);
    requires x1 == int_of_Z(z1) &*& x2 == int_of_Z(z2);
    ensures (x1 & x2) == int_of_Z(Z_and(z1, z2));

lemma void test()
    requires true;
    ensures 0 == (0x01 & 0x10);
{
    bitand_def(0x01, 0x10, digit(sign(false), true), digit(digit(digit(digit(digit(sign(false), true), false), false), false), false));
}

lemma Z Z_of_uint8(int x);
    requires 0 <= x &*& x <= 255;
    ensures result == digit(digit(digit(digit(digit(digit(digit(digit(sign(false), _), _), _), _), _), _), _), _) &*& x == int_of_Z(result);

lemma void Z_of_uint8_eq(Z z1, Z z2)
    requires z1 == digit(digit(digit(digit(digit(digit(digit(digit(sign(false), ?b7), ?b6), ?b5), ?b4), ?b3), ?b2), ?b1), ?b0) &*& z2 == digit(digit(digit(digit(digit(digit(digit(digit(sign(false), b7), b6), b5), b4), b3), b2), b1), b0);
    ensures z1 == z2;
{
}

lemma void bitand_uint8_symm(int x, int y)
    requires 0 <= x &*& x <= 255 &*& 0 <= y &*& y <= 255;
    ensures (x & y) == (y & x);
{
    Z zx = Z_of_uint8(x);
    Z zy = Z_of_uint8(y);
    bitand_def(x, y, zx, zy);
    bitand_def(y, x, zy, zx);
    Z_of_uint8_eq(Z_and(zx, zy), Z_and(zy, zx));
}

@*/
