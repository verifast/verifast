#pragma once

bool isTrue(bool b);
//@ requires true;
//@ ensures true &*& result == b;

bool isTrue(int i);
//@ requires true;
//@ ensures true &*& result == (i == 0 ? false : true);

struct Overloads {
  Overloads()
  //@ requires true;
  //@ ensures true;
  {}
  
  ~Overloads()
  //@ requires true;
  //@ ensures true;
  {}

  bool isTrue(bool b);
  //@ requires true;
  //@ ensures true &*& result == b;

  bool isTrue(int i);
  //@ requires true;
  //@ ensures true &*& result == (i == 0 ? false : true);
};