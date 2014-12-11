#include "simple_termination1.h"

void baz(int n)
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    for (int i = 0; i < n; i++)
        //@ invariant true;
        //@ decreases n - i;
    {
        foo();
        bar();
    }
}