#include <stdlib.h>
#include <stdint.h>

void test(uint32_t *p)
//@ requires integer_(p, 4, false, _);
//@ ensures *p |-> _; //~should_fail
{}

int main()
//@ requires true;
//@ ensures false;
{
  int i = 0;
  int *p = &i;
  int16_t *q = (void *)p;
  *p = 42;
  //@ open integer(p, 42);
  //@ open int_(p, some(42));
  //@ integer__to_chars(p, 4, true);
  //@ chars_to_integer_(q, 2, true);
  *q = 0; //~should_fail This is Undefined Behavior. It can lead to miscompilation: https://godbolt.org/z/Yz6z1G6f5
  //@ assert false;
}
