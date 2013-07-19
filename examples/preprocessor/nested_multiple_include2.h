#ifndef NESTED_MULTIPLE_INCLUDE2_H
#define NESTED_MULTIPLE_INCLUDE2_H

#include "stdlib.h"

/*@
#define ASSERT_TRUE(x) \
   x == true

#define OWNERSHIP(x,y,z) \
   Ownership(x)(y,z)
@*/

/*
  Destructors
*/

/*@

predicate_family OWNERSHIP(void* destructor, void* data, any info);

@*/

typedef void destructor(void* data);
  //@ requires OWNERSHIP(this, data, _);
  //@ ensures emp;

/*
  Stack
*/

struct node
{
  void* data;
  struct node* next;
};

struct stack
{
  struct node* first;
  destructor* destructor;
  int size;
};

#endif
