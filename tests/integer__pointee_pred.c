#include <stdint.h>

#if UINT_MAX != UINT16_MAX || UINTPTR_MAX != UINT16_MAX
  #error This file assumes a 16-bit architecture
#endif

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

void bar(int32_t *p)
//@ requires p[..3] |-> {10, 20, 30};
//@ ensures p[..3] |-> {11, 21, 31};
{
    (*p)++; p++;
    (*p)++; p++;
    (*p)++; p++;
}

void baz(int32_t *p)
//@ requires p[..3] |-> {10, 20, 30};
//@ ensures p[..3] |-> {11, 21, 31};
{
    p[0]++;
    p[1]++;
    p[2]++;
}

void quux()
//@ requires true;
//@ ensures true;
{
    uint32_t xs[3] = {444, 333, 222};
    //@ assert xs[..3] |-> {444, 333, 222};
}

void foo3(int32_t *p1, int128_t *p2)
//@ requires p1 == (void *)p2 &*& [1/2]*p1 |-> _ &*& [1/2]*p2 |-> _;
//@ ensures *p1 |-> _; //~ should_fail
{
}
