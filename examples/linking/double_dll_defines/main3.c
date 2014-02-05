#include "dll.h"

#include "stdlib.h"
#include "stdio.h"

struct struct_dll
{
  int foo;
};

int main()  //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct struct_dll* s1 = get_struct_dll();
  free_struct_dll(s1);
  return 0;
}
