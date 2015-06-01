#include "test.h"

#include <malloc.h>

int main() //@ : main()
  //@ requires true;
  //@ ensures true;
{
  void *b = malloc(1);
  if (b != 0)
  {
    //@ assert custom_chars(b, 1, _);
    free(b);
  }
  
  test();
  
  return 0;
}