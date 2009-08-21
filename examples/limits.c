void foo(int x)
    //@ requires true;
    //@ ensures true;
{
    //@ produce_limits(x);
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
}