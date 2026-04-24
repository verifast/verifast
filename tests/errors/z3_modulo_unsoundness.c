// Z3's built-in `mod` is Euclidean; C99 `%` is truncated toward zero.

void test(int x)
//@ requires x < 0 &*& x > -100;
//@ ensures true;
{
    int r = x % 2;
    //@ assert r >= 0; //~ should_fail
}
