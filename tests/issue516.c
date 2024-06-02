#include <stdint.h>
#include <stdio.h>

int main()
//@ requires true;
//@ ensures true;
{
  uint32_t var = 122;
  printf("var = 0x%x\n", var);
  return 0;
}
