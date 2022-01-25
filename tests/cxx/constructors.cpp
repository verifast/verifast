#include "constructors.h"

Test::Test(int i) : _i(i)
//@ requires true;
//@ ensures TestPred(this, i, _);
{
  //@ close TestPred(this, i, _);
}

int main()
//@ requires true;
//@ ensures true;
{
  Test *mi = new Test(2);
  Test *mii = new Test;
  delete mi;
  delete mii;
}