#ifndef MULTIPLE_INCLUDE2_H
#define MULTIPLE_INCLUDE2_H

#include "multiple_include3.h"

void decrement(int* count)
  //@ requires integer(count,?count0);
  //@ ensures integer(count,count0 - 1);
{
  (*count)--;
}

#endif
