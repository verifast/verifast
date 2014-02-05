#ifndef NONABSTRACT_PRED_H
#define NONABSTRACT_PRED_H

//@ predicate test() = true;

void func();
  //@ requires true;
  //@ ensures  test();

#endif
