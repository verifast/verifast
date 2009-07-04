#include "stdlib.h"
#include "counter_spec.h"

int main() 
  //@ requires true;
  //@ ensures true;
{
  struct counter* c1 = create_counter();
  inc(c1);
  struct counter* c2 = create_counter();
  inc(c2);
  inc(c2);
  swap(c1, c2);
  int tmp = counter_get(c1);
  
  dispose(c1);
  dispose(c2);
  
  //@ assert tmp == 2;

  return 0;
}