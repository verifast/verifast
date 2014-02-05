#ifndef STRUCT_BODY_H
#define STRUCT_BODY_H

struct test
{
  int body;
};

void func(struct test* t);
  //@ requires t->body |-> _;
  //@ ensures  t->body |-> 1;

#endif
