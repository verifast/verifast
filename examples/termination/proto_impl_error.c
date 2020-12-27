#include "proto_impl_error.h"

void should_terminate() //~ should_fail
    //@ requires true;
    //@ ensures true;
{
    for (;;) //~allow_dead_code
        //@ invariant true;
    {
    }
}