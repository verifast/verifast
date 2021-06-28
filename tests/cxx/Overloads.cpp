#include "Overloads.h"

bool isTrue(bool b)
//@ requires true;
//@ ensures true &*& result == b;
{
  return b;
}

bool isTrue(int i)
//@ requires true;
//@ ensures true &*& result == (i == 0 ? false : true);
{
  return i != 0;
}

bool Overloads::isTrue(bool b)
//@ requires true;
//@ ensures true &*& result == b;
{
  return ::isTrue(b);
}

bool Overloads::isTrue(int i)
//@ requires true;
//@ ensures true &*& result == (i == 0 ? false : true);
{
  return ::isTrue(i);
}

int main()
//@ requires true;
//@ ensures true;
{
  Overloads *ovls = new Overloads;
  bool result;
  result = ovls->isTrue(0);
  //@ assert !result;
  result = ovls->isTrue(1);
  //@ assert result;
  result = ovls->isTrue(false);
  //@ assert !result;
  result = ovls->isTrue(true);
  //@ assert result;

  //@ leak new_block_Overloads(ovls);
}