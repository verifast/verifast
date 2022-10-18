#include "dll1.h"

#include "stdlib.h"
#include "stdio.h"

struct struct_dll1
{
  int body;
};

/*@ predicate predicate_dll1(struct struct_dll1* s) =
      malloc_block_struct_dll1(s) &*& 
      struct_dll1_body_(s, ?value);
@*/

struct struct_dll1* get_struct_dll1()
  //@ requires true;
  //@ ensures predicate_dll1(result);
{
  printf("get_struct_dll1\n");
  struct struct_dll1 *result = malloc(sizeof(struct struct_dll1));
  if (result == 0) abort();
  //@ close predicate_dll1(result);
  return result;
}

void free_struct_dll1(struct struct_dll1 *s)
  //@ requires predicate_dll1(s);
  //@ ensures true;
{
  printf("free_struct_dll1\n");
  //@ open predicate_dll1(s);
  free(s);
}
