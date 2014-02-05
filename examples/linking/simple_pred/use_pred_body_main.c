#include "nonabstract_pred.h"

int main() //@ : main
  //@ requires true;
  //@ ensures  true;
{
  func();
  //@ open test();
  return 0;
}
