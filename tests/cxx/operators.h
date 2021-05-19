#pragma once

class IntWrapper {
  int i = 0;

  public:
  void setInt(int i);
  //@ requires this->i |-> _;
  //@ ensures this->i |-> i;

  int getInt() const;
  //@ requires [?f]this->i |-> ?i;
  //@ ensures [f]this->i |-> i &*& result == i;
  
  operator int() const;
  //@ requires [?f]this->i |-> ?i;
  //@ ensures [f]this->i |-> i &*& result == i;

  bool operator<(int other);
  //@ requires [?f]this->i |-> ?i;
  //@ ensures [f]this->i |-> i &*& result == (i < other);

  bool operator>(int other);
  //@ requires [?f]this->i |-> ?i;
  //@ ensures [f]this->i |-> i &*& result == (i > other);
  
};