#include "simple_termination1.h"

void foo()
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    for (int i = 0; i < 10; i++)
        //@ invariant true;
        //@ decreases 10 - i;
    {
    }
}

void bar()
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    for (int i = 0; i < 10; i++)
        //@ invariant true;
        //@ decreases 10 - i;
    {
        foo();
    }
}
