#include "dll.h"

#include "stdlib.h"

int main()  //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct struct_dll* s1 = get_struct_dll();
  free_struct_dll(s1);
  return 0;
}
