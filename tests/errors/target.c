#include <assert.h>

void foo()
//@ requires true;
//@ ensures true;
{
  assert(sizeof(int) == 4 || sizeof(void *) == 4); //~should_fail
}

void bar()
//@ requires true;
//@ ensures true;
{
  assert(sizeof(long) == 4); //~should_fail
}