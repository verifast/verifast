#include "dll1.h"

#include "stdlib.h"

int main()  //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct struct_global *s0 = malloc(sizeof(struct struct_global));
  if (s0 == 0) abort();
  free(s0);
  
  struct struct_dll1* s1 = get_struct_dll1();
  free_struct_dll1(s1);
  struct struct_dll2* s2 = get_struct_dll2_stub();
  free_struct_dll2_stub(s2);
  struct struct_dll2* s3 = get_struct_dll2();
  free_struct_dll2(s3);
  return 0;
}
