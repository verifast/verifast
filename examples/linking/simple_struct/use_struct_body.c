#include "struct_body.h"

void func(struct test* t)
  //@ requires t->body |-> _;
  //@ ensures  t->body |-> 1;
{
  t->body = 1;  
}
