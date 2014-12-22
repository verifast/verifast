//@ predicate unsound() = false;

void func();
  //@ requires true;
  //@ ensures unsound();

