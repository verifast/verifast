#include "dll.h"

#include "stdlib.h"
#include "stdio.h"

void func()
  //@ requires true;
  //@ ensures  true;
{
  
}

int main()  //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct struct_dll* s1 = get_struct_dll();
  free_struct_dll(s1);
  return 0;
}
