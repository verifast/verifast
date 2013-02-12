#ifndef MULTIPLE_INCLUDE3_H
#define MULTIPLE_INCLUDE3_H

void reset(int* count)
  //@ requires integer(count,?count0);
  //@ ensures integer(count,0);
{
  (*count) = 0;
}

#endif