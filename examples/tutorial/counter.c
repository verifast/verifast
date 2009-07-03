#include "stdlib.h"

struct counter {
  int x;
};

int main() 
  //@ requires true;
  //@ ensures true;
{
  struct counter* c = malloc(sizeof(struct counter));
  c->x = 10;

  return 0;
}