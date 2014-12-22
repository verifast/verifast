//@ predicate unsound() = true;

void func();
  //@ requires true;
  //@ ensures unsound();

