#include <stdint.h>

struct foo {
  int bar;
  int baz;
};

int main()
//@ requires true;
//@ ensures true;
{
  struct foo myFoo = { 0, 0 };
  int *myFoo_bar_ptr = &myFoo.bar;
  return 0;
}
