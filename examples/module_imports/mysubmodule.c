
#include "mysubmodule.h"

/*@
  predicate mysubmodule_state(int ctr) =
    integer(&counter, ctr) &*& ctr >= 0;
@*/

static int counter;

void mysubmodule_init()
//@ requires module(mysubmodule, true);
//@ ensures mysubmodule_state(0);
{
  //@ open_module();
  counter = 0;
  //@ close mysubmodule_state(0);
}

void mysubmodule_increment()
//@ requires mysubmodule_state(?ctr);
//@ ensures ctr == INT_MAX ? mysubmodule_state(ctr) : mysubmodule_state(ctr + 1);
{
  //@ open mysubmodule_state(ctr);
  //@ produce_limits(counter);
  if (counter < INT_MAX) {
    counter = counter + 1;
    //@ close mysubmodule_state(ctr + 1);
  } else {
    //@ close mysubmodule_state(ctr);
  }
}

int mysubmodule_get()
//@ requires mysubmodule_state(?ctr);
//@ ensures mysubmodule_state(ctr) &*& result == ctr;
{
  //@ open mysubmodule_state(ctr);
  return counter;
  //@ close mysubmodule_state(ctr);
}

void mysubmodule_destroy()
//@ requires mysubmodule_state(_);
//@ ensures module(mysubmodule, false);
{
  //@ open mysubmodule_state(_);
  //@ close_module();
}
