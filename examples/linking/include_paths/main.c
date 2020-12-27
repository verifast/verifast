#include "header.h"

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  func();
  //@ open unsound();
  *((int*) 0) = 5; //~allow_dead_code
  
  return 0; //~allow_dead_code
}


