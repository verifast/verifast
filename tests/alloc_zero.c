#include <malloc.h>

void test()
//@ requires true;
//@ ensures true;
{
    void* p = malloc(0);
    if(p) {
        //@ assert object_pointer_within_limits(p,0) == true;
        //@ assert false; //~should_fail
    }
}

