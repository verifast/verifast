// Test that circular includes are not allowed

#include "bad_circular_include.h"

int foo0 ()
    //@ requires true;
    //@ ensures result == 0; 
{
    return 0;
}

