#define PRE false
#include "lib.h"

void foo()
    //@ requires false;
    //@ ensures true;
{
    int *p = 0;
    *p = 42;
}
