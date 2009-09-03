void foo(bool a, bool b, bool c)
    //@ requires a == b &*& true == (b ? c : true);
    //@ ensures c; //~ should_fail
{
}
