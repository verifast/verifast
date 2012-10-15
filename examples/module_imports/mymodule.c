#include "stdlib.h"

#include "mymodule.h"

#include "mysubmodule.h"

//@ import_module mysubmodule;

static int value;

/*@
  predicate mymodule_state(int x, int ctr) =
    integer(&value, x) &*& mysubmodule_state(ctr);
@*/


void mymodule_init()
//@ requires module(mymodule, true);
//@ ensures mymodule_state(0, 0);
{
  //@ open_module();
  mysubmodule_init();
  value = 0;
  //@ close mymodule_state(0, 0);
}

void mymodule_destroy()
//@ requires mymodule_state(_, _);
//@ ensures module(mymodule, false);
{
  //@ open mymodule_state(_, _);
  mysubmodule_destroy();
  //@ close_module();
}

void mymodule_set(int val)
//@ requires mymodule_state(_, ?ctr);
//@ ensures ctr == INT_MAX ? mymodule_state(val, ctr) : mymodule_state(val, ctr + 1);
{
  //@ open mymodule_state(_, ctr);
  value = val;
  mysubmodule_increment();
  int ctr_val = mysubmodule_get();
  if (ctr_val == INT_MAX) {
    //@ close mymodule_state(val, INT_MAX);
  } else {
    //@ close mymodule_state(val, ctr + 1);
  }
}

int mymodule_get()
//@ requires mymodule_state(?x, ?ctr);
//@ ensures mymodule_state(x, ctr) &*& result == x;
{
  //@ open mymodule_state(x, ctr);
  return value;
  //@ close mymodule_state(x, ctr);
}

int mymodule_get_count()
//@ requires mymodule_state(?x, ?ctr);
//@ ensures mymodule_state(x, ctr) &*& result == ctr;
{
  //@ open mymodule_state(x, ctr);
  return mysubmodule_get();
  //@ close mymodule_state(x, ctr);
}
