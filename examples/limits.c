void foo(int x)
    //@ requires true;
    //@ ensures true;
{
    // //@ produce_limits(x); // no longer needed
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
}