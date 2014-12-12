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
        //@ assert func_lt(foo, baz) == true;
        //@ assert func_lt(bar, baz) == true;
    }
}

void baz2(int n)
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
        //@ assert func_lt(foo, baz) == true;
        //@ assert func_lt(bar, baz) == true;
    }
}