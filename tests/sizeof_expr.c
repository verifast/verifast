#include <stdlib.h>

void test()
//@ requires true;
//@ ensures true;
{
  char buf[100];
  for (size_t i = 0; i < sizeof(buf); i++)
  //@ invariant 0 <= i &*& i <= sizeof(buf) &*& buf[..sizeof(buf)] |-> _;
    buf[i] = 0;
}

#define LEN(xs) (sizeof(xs)/sizeof(xs[0]))

void test2()
//@ requires true;
//@ ensures true;
{
  int buf[100];
  for (size_t i = 0; i < sizeof(buf)/sizeof(buf[0]); i++)
  //@ invariant 0 <= i &*& i <= LEN(buf) &*& buf[..LEN(buf)] |-> _;
    buf[i] = 0;
}
