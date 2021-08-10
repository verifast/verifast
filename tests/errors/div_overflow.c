int div_overflow(int x, int y)
    //@ requires y != 0;
    //@ ensures true;
{
    return x / y; //~ should_fail
}