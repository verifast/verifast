
#ifndef MYMODULE_H
#define MYMODULE_H

//@ require_module mymodule;
//@ predicate mymodule_state(int x, int ctr);

void mymodule_init();
//@ requires module(mymodule, true);
//@ ensures mymodule_state(0, 0);

void mymodule_destroy();
//@ requires mymodule_state(_, _);
//@ ensures module(mymodule, false);

void mymodule_set(int value);
//@ requires mymodule_state(_, ?ctr);
//@ ensures ctr == INT_MAX ? mymodule_state(value, ctr) : mymodule_state(value, ctr + 1);

int mymodule_get();
//@ requires mymodule_state(?x, ?ctr);
//@ ensures mymodule_state(x, ctr) &*& result == x;

int mymodule_get_count();
//@ requires mymodule_state(?x, ?ctr);
//@ ensures mymodule_state(x, ctr) &*& result == ctr;

#endif
