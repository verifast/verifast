#include "multiple_include.h"
#include "multiple_include2.h"
#include "multiple_include.h"

int main() //@ : main
  //@ requires true;
  //@ ensures true; 
{
  int count = 20;
  increment(&count);
  decrement(&count);
  //@ assert count == 20;
  return 0;
}
