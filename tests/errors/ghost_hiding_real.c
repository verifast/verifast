int x;

void test1()
//@ requires x |-> 0;
//@ ensures x |-> 0;
{
    //@ int x = 0;
    x = 5; //~ should_fail
}

void test1_1()
//@ requires x |-> 0;
//@ ensures x |-> 0;
{
    //@ int x = 0;
    *&x = 5; //~ should_fail
}

int test2()
//@ requires x |-> 0;
//@ ensures x |-> 0 &*& result == 5;
{
    //@ int x = 5;
    return x; //~ should_fail
}

int test2_1()
//@ requires x |-> 0;
//@ ensures x |-> 0 &*& result == 5;
{
    //@ int x = 5;
    return *&x; //~ should_fail
}