#include "dll2.h"

#include "stdlib.h"
#include "stdio.h"

struct struct_dll2
{
  int body;
};

/*@ predicate predicate_dll2(struct struct_dll2* s) =
      malloc_block_struct_dll2(s) &*& 
      struct_dll2_body_(s, _);
@*/

struct struct_dll2* get_struct_dll2()
  //@ requires true;
  //@ ensures predicate_dll2(result);
{
  printf("get_struct_dll2\n");
  struct struct_dll2 *result = malloc(sizeof(struct struct_dll2));
  if (result == 0) abort();
  //@ close predicate_dll2(result);
  return result;
}

void free_struct_dll2(struct struct_dll2 *s)
  //@ requires predicate_dll2(s);
  //@ ensures true;
{
  printf("free_struct_dll2\n");
  //@ open predicate_dll2(s);
  free(s);
}
