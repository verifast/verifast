#include <stdint.h>

void foo1(int32_t *p1, int128_t *p2)
//@ requires [1/2]*p1 |-> 10 &*& [1/2]*p2 |-> 20;
//@ ensures [1/2]*p1 |-> 10 &*& [1/2]*p2 |-> 20;
{
}

void foo2(int32_t *p)
//@ requires *p |-> 0;
//@ ensures *p |-> 2;
{
    (*p)++;
    *p = *p + 1;
}

void foo2bis(int128_t *p)
//@ requires *p |-> 0;
//@ ensures *p |-> 2;
{
    (*p)++;
    *p = *p + 1;
}

void foo3(int32_t *p1, int128_t *p2)
//@ requires p1 == (void *)p2 &*& [1/2]*p1 |-> _ &*& [1/2]*p2 |-> _;
//@ ensures *p1 |-> _; //~ should_fail
{
}
