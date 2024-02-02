#include <stdint.h>

void swap<T>(T *p1, T *p2)
//@ requires *p1 |-> ?v1 &*& *p2 |-> ?v2;
//@ ensures *p1 |-> v2 &*& *p2 |-> v1;
{
  T tmp = *p1;
  *p1 = *p2;
  *p2 = tmp;
}

void swap_int32(int32_t *p1, int32_t *p2)
//@ requires *p1 |-> ?v1 &*& *p2 |-> ?v2;
//@ ensures *p1 |-> v2 &*& *p2 |-> v1;
{
  swap<int32_t>(p1, p2);
}
