#include "stdlib.h"

struct counter {
  int x;
};

struct counter* create_counter() 
  //@ requires false;
  //@ ensures true;
{
  struct counter* c = malloc(sizeof(struct counter));
  if(c == 0) { abort(); }
  c->x = 0;
  return c;
}

void inc(struct counter* c)
  //@ requires false;
  //@ ensures true;
{
  int tmp = c->x;
  c->x = tmp + 1;
}

int get(struct counter* c)
  //@ requires false;
  //@ ensures true; 
{
  int tmp = c->x;
  return tmp;
}

void swap(struct counter* c1, struct counter* c2)
  //@ requires false;
  //@ ensures true;
{
  int tmp = c1->x;
  c1->x = c2->x;
  c2->x = tmp;
}

void dispose(struct counter* c)
  //@ requires false;
  //@ ensures true;
{
  free(c);
}

int main() 
  //@ requires true;
  //@ ensures true;
{
  struct counter* c = malloc(sizeof(struct counter));
  c->x = 10;
  int tmp = c->x;
  assert(tmp == 10);
  return 0;
}
