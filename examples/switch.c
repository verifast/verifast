#include "stdlib.h"

enum numbers { zero, one, two };

void m(int i) 
  //@ requires true;
  //@ ensures true;
{
  int j = 0;
  switch(i) {
    case one:
      j = 2;
      break;
    case two:
      j = 2;
      break;
    default:
      j = 3;
      break;
  }
  if(i == 1 || i == 2) {
    assert(j == 2);
  } else {
    assert(j == 3);
  } 
}

void n(int i)
  //@ requires true;
  //@ ensures true;
{
  int j = 0;
  int t = 0;
  switch(i) {
    case 1:
      j = 1;
    case 2:
      j = 2;
      t = 2;
      break;
  }
  assert(j == 2 && t == 2 || j == 0 && t == 0);
}