#include "struct_body.h"

#include "stdlib.h"

int main() //@ : main
  //@ requires true;
  //@ ensures  true;
{
  struct test* t = malloc(sizeof(struct test));
  if (t == 0) {abort();}
  func(t);
  //@ assert t->body == 1;
  free(t);
  return 0;
}
