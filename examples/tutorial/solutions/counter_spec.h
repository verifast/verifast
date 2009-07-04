#ifndef COUNTER_H
#define COUNTER_H

#include "stdlib.h"

struct counter;

/*@
predicate counter(struct counter* c, int v);
@*/

struct counter* create_counter();
  //@ requires true;
  //@ ensures counter(result, 0);

void inc(struct counter* c);
  //@ requires counter(c, ?v);
  //@ ensures counter(c, v + 1);
  
void swap(struct counter* c1, struct counter* c2);
  //@ requires counter(c1, ?v1) &*& counter(c2, ?v2);
  //@ ensures counter(c1, v2) &*& counter(c2, v1);

int counter_get(struct counter* c);
  //@ requires counter(c, ?v);
  //@ ensures counter(c, v) &*& result == v;

void dispose(struct counter* c);
  //@ requires counter(c, ?v);
  //@ ensures true;

#endif