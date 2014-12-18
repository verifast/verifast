void fob()
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    for (;;) //~ should_fail
        //@ invariant true;
    {
    }
}

void foo()
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    foo(); //~ should_fail
}

void bar()
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    baz(); //~ should_fail
}

void baz()
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    bar();
}

