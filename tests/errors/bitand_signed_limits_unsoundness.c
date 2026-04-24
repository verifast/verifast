// `bitand_signed_limits` used to accept either operand in range, but signed
// AND of an out-of-range positive with an in-range negative can exceed the
// range. E.g. (3 & -2) == 2 falls outside [-2, 2).

//@ #include <bitops.gh>
//@ #include <nat.gh>

void exploit()
//@ requires true;
//@ ensures true;
{
    int x = 3;
    int y = -2;
    int z = x & y;
    //@ bitand_signed_limits(x, y, succ(zero)); //~ should_fail
}
