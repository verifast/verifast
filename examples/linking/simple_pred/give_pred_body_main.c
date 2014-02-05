#include "abstract_pred.h"

//@ predicate test() = true;

void test()
  //@ requires true;
  //@ ensures  test();
{
  //@ close test();
}

int main() //@ : main
  //@ requires true;
  //@ ensures  true;
{
  test();
  //@ open test();
  return 0;
}
