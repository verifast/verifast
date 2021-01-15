// verifast_options{target:LP64}

void test()
    //@ requires true;
    //@ ensures true;
{
    assert(sizeof(void *) == 8);
}
