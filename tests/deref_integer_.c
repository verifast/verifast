#include <stdlib.h>
#include <assert.h>

void test()
//@ requires true;
//@ ensures true;
{
  size_t x = 0;
  size_t *p = &x;
  assert(*p == 0);
  //@ open uintptr(p, _);
  //@ open uintptr_(p, _);
  //@ integer___limits(p);
  assert(p != 0);
}
