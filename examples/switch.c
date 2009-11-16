#include "stdlib.h"

// note: switch statements only work if break statements are written in each case!

void m(int i) 
  //@ requires true;
  //@ ensures true;
{
  int j = 0;
  switch(i) {
    case 1:
      j = 2;
      break;
    case 2:
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