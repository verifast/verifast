#include "stdlib.h"
#include "counter_spec.h"

struct counter {
  int x;
};

/*@
predicate counter(struct counter* c, int v)
  requires c->x |-> v &*& malloc_block_counter(c);
@*/

struct counter* create_counter()
  //@ requires true;
  //@ ensures counter(result, 0);
{
  struct counter* c = malloc(sizeof(struct counter));
  if(c == 0) { abort(); }
  c->x = 0;
  //@ close counter(c, 0);
  return c;
}

void inc(struct counter* c)
  //@ requires counter(c, ?v);
  //@ ensures counter(c, v + 1);
{
  //@ open counter(c, v);
  c->x = c->x + 1;
  //@ close counter(c, v + 1);
}

void swap(struct counter* c1, struct counter* c2)
  //@ requires counter(c1, ?v1) &*& counter(c2, ?v2);
  //@ ensures counter(c1, v2) &*& counter(c2, v1);
{
  //@ open counter(c1, v1);
  //@ open counter(c2, v2);
  int tmp = c1->x;
  c1->x = c2->x;
  c2->x = tmp;
  //@ close counter(c1, v2);
  //@ close counter(c2, v1);
}

int counter_get(struct counter* c)
  //@ requires counter(c, ?v);
  //@ ensures counter(c, v) &*& result == v;
{
  //@ open counter(c, v);
  int tmp = c->x;
  //@ close counter(c, v);
  return tmp;
}

void dispose(struct counter* c)
  //@ requires counter(c, ?v);
  //@ ensures true;
{
  //@ open counter(c, v);
  free(c);
}