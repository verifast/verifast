void test()
    //@ requires true;
    //@ ensures true;
{
    assert(sizeof(void *) == 8);
}
