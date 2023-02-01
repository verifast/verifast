#include <stdint.h>

int main()
//@ requires true;
//@ ensures true;
{
  int32_t *i = new int32_t;
  *i = 2;
  delete i;
}
