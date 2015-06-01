#include "test.h"

#include <malloc.h>

void test()
  //@ requires true;
  //@ ensures true;
{
  void *b = malloc(1);
  if (b != 0)
  {
    //@ assert custom_chars(b, 1, _);
    free(b);
  }
}