// Regression for a copy-paste typo: `bitxor_signed_limits` used to bound (x | y).

//@ #include <bitops.gh>
//@ #include <nat.gh>

void test_bitxor_bounds(int x, int y)
    //@ requires -2 <= x &*& x < 2 &*& -2 <= y &*& y < 2;
    //@ ensures true;
{
    int z = x ^ y;
    //@ bitxor_signed_limits(x, y, succ(zero));
    //@ assert -2 <= z &*& z < 2;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
