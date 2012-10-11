#include "stdlib.h"

#include "mymodule.h"

struct counter {
  int f;
};

/*@
  predicate counter(struct counter *c, int value) =
    malloc_block_counter(c) &*& c->f |-> value;
@*/


static int x;
static struct counter *c;

/*@
  predicate mymodule_state(int x0, int ctrf) =
    integer(&x, x0) &*& pointer(&c, ?ctr) &*& counter(ctr, ctrf);
@*/


void mymodule_init()
//@ requires module(mymodule, true);
//@ ensures mymodule_state(0, 0);
{
  //@ open_module();
  x = 0;
  c = malloc(sizeof(struct counter));
  if (c == 0) abort();
  c->f = 0;
  //@ close counter(c, 0);
  //@ close mymodule_state(0, 0);
}

void mymodule_destroy()
//@ requires mymodule_state(_, _);
//@ ensures module(mymodule, false);
{
  //@ open mymodule_state(_, _);
  //@ open counter(c, _);
  free(c);
  //@ close_module();
}

void mymodule_set(int value)
//@ requires mymodule_state(_, ?ctr_val);
//@ ensures ctr_val == INT_MAX ? mymodule_state(value, ctr_val) : mymodule_state(value, ctr_val + 1);
{
  //@ open mymodule_state(_, ctr_val);
  x = value;
  //@ open counter(c, ctr_val);
  if (c->f < INT_MAX) {
    c->f += 1;
    //@ close counter(c, ctr_val + 1);
    //@ close mymodule_state(value, ctr_val + 1);
  } else {
    //@ close counter(c, ctr_val);
    //@ close mymodule_state(value, ctr_val);
  }
}

int mymodule_get()
//@ requires mymodule_state(?x0, ?ctr_val);
//@ ensures mymodule_state(x0, ctr_val) &*& result == x0;
{
  //@ open mymodule_state(x0, ctr_val);
  return x;
  //@ close mymodule_state(x0, ctr_val);
}
