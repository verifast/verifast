int div_by_zero(int x, int y)
    //@ requires true;
    //@ ensures true;
{
    return x / y; //~ should_fail
}

int mod_by_zero(int x, int y)
    //@ requires true;
    //@ ensures true;
{
    return x % y; //~ should_fail
}
