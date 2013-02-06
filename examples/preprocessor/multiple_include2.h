#ifndef MULTIPLE_INCLUDES2_H
#define MULTIPLE_INCLUDES2_H

void decrement(int* count)
  //@ requires integer(count,?count0);
  //@ ensures integer(count,count0 - 1);
{
  (*count)--;
}

#endif
