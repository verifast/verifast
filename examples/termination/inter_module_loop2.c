#include "inter_module_loop.h"

int sqrt2(int x)
    //@ requires 0 <= x;
    //@ ensures result * result <= x && x < (result + 1) * (result + 1);
    //@ terminates;
{
    return sqrt1(x);
}