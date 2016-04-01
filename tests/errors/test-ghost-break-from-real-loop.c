void foo()
    //@ requires true;
    //@ ensures true;
{
    while (true)
        //@ invariant true;
    {
        //@ break; //~ should_fail
        assert(false);
    }
}
