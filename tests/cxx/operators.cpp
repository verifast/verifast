#include "operators.h"

void IntWrapper::setInt(int i)
//@ requires this->i |-> _;
//@ ensures this->i |-> i;
{
  this->i = i;
}

int IntWrapper::getInt() const
//@ requires [?f]this->i |-> ?i;
//@ ensures [f]this->i |->i &*& result == i;
{
  return i;
}

IntWrapper::operator int() const
//@ requires [?f]this->i |-> ?i;
//@ ensures [f]this->i |-> i &*& result == i;
{
  return this->i;
}

bool IntWrapper::operator<(int other)
//@ requires [?f]this->i |-> ?i;
//@ ensures [f]this->i |-> i &*& result == (i < other);
{
  return i < other;
}

bool IntWrapper::operator>(int other)
//@ requires [?f]this->i |-> ?i;
//@ ensures [f]this->i |-> i &*& result == (i > other);
{
  return i > other;
}

int main()
//@ requires true;
//@ ensures true;
{
  IntWrapper *iw = new IntWrapper;
  iw->setInt(5);
  int iw_val = *iw; // implicit conversion to int
  int ten = 5 + iw_val;
  //@ assert ten == 10;
  bool lt = (*iw) < 6; // operator overload <
  //@ assert lt;
  bool gt = (*iw) > 4; // operator overload >
  //@ assert gt;
  delete iw;
}