
#ifndef MYMODULE_H
#define MYMODULE_H

//@ import_module mymodule;
//@ predicate mymodule_state(int x, int ctr_val);

void mymodule_init();
//@ requires module(mymodule, true);
//@ ensures mymodule_state(0, 0);

void mymodule_destroy();
//@ requires mymodule_state(_, _);
//@ ensures module(mymodule, false);

void mymodule_set(int value);
//@ requires mymodule_state(_, ?ctr_val);
//@ ensures ctr_val == INT_MAX ? mymodule_state(value, ctr_val) : mymodule_state(value, ctr_val + 1);

int mymodule_get();
//@ requires mymodule_state(?x0, ?ctr_val);
//@ ensures mymodule_state(x0, ctr_val) &*& result == x0;


#endif
