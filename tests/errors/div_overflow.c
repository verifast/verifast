int div_overflow(int x, int y)
    //@ requires y != 0;
    //@ ensures true;
{
    return x / y; //~ should_fail
}

int mod_no_overflow(int x, int y)
    //@ requires y != 0 &*& !(x == INT_MIN && y == -1);
    //@ ensures result == x % y;
{
    return x % y;
}

int mod_overflow(int x, int y)
    //@ requires y != 0;
    //@ ensures true;
{
    return x % y; //~ should_fail
}
