#ifndef MULTIPLE_INCLUDE_H
#define MULTIPLE_INCLUDE_H

#include "multiple_include2.h"
#include "multiple_include3.h"

void increment(int* count)
  //@ requires integer(count,?count0);
  //@ ensures integer(count,count0 + 1);
{
  (*count)++;
}

#endif