#include "inter_module_loop.h"

int sqrt1(int x)
    //@ requires 0 <= x;
    //@ ensures result * result <= x && x < (result + 1) * (result + 1);
    //@ terminates;
{
    return sqrt2(x);
}