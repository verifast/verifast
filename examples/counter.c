#include "stdlib.h"

struct Counter {
  int value;
};

struct Counter* init(int v)
  //@ requires emp;
  //@ ensures result->value |-> v &*& malloc_block_Counter(result);
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  return c;
}

void increment(struct Counter* c)
  //@ requires c->value |-> ?v;
  //@ ensures c->value |-> v + 1;
{
  int tmp = c->value;
  c->value = tmp + 1;
}

void dispose(struct Counter* c)
  //@ requires c->value |-> _ &*& malloc_block_Counter(c);
  //@ ensures emp;
{
  free(c);
}

void swap(struct Counter* c1, struct Counter* c2)
  //@ requires c1->value |-> ?v1 &*& c2->value |-> ?v2;
  //@ ensures c1->value |-> v2 &*& c2->value |-> v1;
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}

int main() //@ : main
  //@ requires emp;
  //@ ensures emp;
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);

  increment(c1); swap(c1, c2); int tmp = c2->value;
  //@ assert tmp == 1;
  
  dispose(c1); dispose(c2);
  return 0;
}



