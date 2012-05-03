#include "stdlib.h"

//@ predicate foo(int x; int y);
//@ predicate bar(int x; int y) = foo(x, y);

void foo()
    //@ requires foo(10, 100);
    //@ ensures foo(10, 100);
{
    //@ close bar(10, ?y);
    //@ open bar(10, y);
}