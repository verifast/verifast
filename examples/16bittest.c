void test()
    //@ requires true;
    //@ ensures true;
{
    int x = 30000;
    x = x + x; //~ should_fail
}
