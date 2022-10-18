#include "dll.h"

#include "stdlib.h"
#include "stdio.h"

struct struct_dll
{
  int body;
};

/*@ predicate predicate_dll(struct struct_dll* s) =
      malloc_block_struct_dll(s) &*& 
      struct_dll_body_(s, ?value);
@*/

void func()
  //@ requires true;
  //@ ensures  true;
{
  
}

struct struct_dll* get_struct_dll()
  //@ requires true;
  //@ ensures predicate_dll(result);
{
  printf("get_struct_dll 2\n");
  struct struct_dll *result = malloc(sizeof(struct struct_dll));
  if (result == 0) abort();
  //@ close predicate_dll(result);
  return result;
}

void free_struct_dll(struct struct_dll *s)
  //@ requires predicate_dll(s);
  //@ ensures true;
{
  printf("free_struct_dll 2\n");
  //@ open predicate_dll(s);
  free(s);
}
