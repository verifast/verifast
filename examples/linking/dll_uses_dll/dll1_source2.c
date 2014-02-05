#include "dll1.h"
#include "dll2.h"

#include "stdio.h"

struct struct_dll2* get_struct_dll2_stub()
  //@ requires true;
  //@ ensures predicate_dll2(result);
{
  printf("get_struct_dll2_stub\n");
  return get_struct_dll2();
}

void free_struct_dll2_stub(struct struct_dll2 *s)
  //@ requires predicate_dll2(s);
  //@ ensures true;
{
  printf("free_struct_dll2_stub\n");
  free_struct_dll2(s);
}
