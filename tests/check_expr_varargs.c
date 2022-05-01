#include <stdio.h>

int foo()
//@ requires true;
//@ ensures true;
{
  return 42;
}

void test()
//@ requires true;
//@ ensures true;
{
  printf("%d\n", foo());
}
