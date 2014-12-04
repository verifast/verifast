#include "header.h"

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  func();
  //@ open unsound();
  *((int*) 0) = 5;
  
  return 0;
}


