#ifndef MYSUBMODULE_H
#define MYSUBMODULE_H

//@ require_module mysubmodule;
//@ predicate mysubmodule_state(int ctr);

void mysubmodule_init();
//@ requires module(mysubmodule, true);
//@ ensures mysubmodule_state(0);

void mysubmodule_increment();
//@ requires mysubmodule_state(?ctr);
//@ ensures ctr == INT_MAX ? mysubmodule_state(ctr) : mysubmodule_state(ctr + 1);

int mysubmodule_get();
//@ requires mysubmodule_state(?ctr);
//@ ensures mysubmodule_state(ctr) &*& result == ctr;

void mysubmodule_destroy();
//@ requires mysubmodule_state(_);
//@ ensures module(mysubmodule, false);

#endif
