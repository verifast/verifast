void foo(int x)
    //@ requires true;
    //@ ensures true;
{
    //@ assume_is_int(x);
    assert(MIN_INT <= x);
    assert(x <= MAX_INT);
}