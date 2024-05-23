#include <stdint.h>

struct foo {
  int bar;
  uint8_t quux[8];
  int baz;
};

int main()
//@ requires true;
//@ ensures true;
{
  struct foo myFoo = { 0, { 0 }, 0 };
  return 0;
}
