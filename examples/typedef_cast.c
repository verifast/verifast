#include <stdint.h>

typedef short my_short;

void foo(int16_t x, my_short y)
    //@ requires true;
    //@ ensures true;
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    void *pv = pz;
    pz = (my_short *)pv;
}
