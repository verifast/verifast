void foo(bool a, bool b, bool c)
    //@ requires true == (a ? b : c);
    //@ ensures b; //~ should_fail
{
}
