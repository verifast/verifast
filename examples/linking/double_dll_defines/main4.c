#include "dll.h"

#include "stdlib.h"
#include "stdio.h"

//@ predicate predicate_dll(struct struct_dll* s) = true;

int main()  //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct struct_dll* s1 = get_struct_dll();
  free_struct_dll(s1);
  return 0;
}
