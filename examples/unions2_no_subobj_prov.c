#include <stdint.h>

typedef union
{
    int i;
    unsigned u;
} union_t;

int main ()
//@ requires true;
//@ ensures true;
{
  union_t x;
  
  //@ chars__to_int_(&x.i);
  x.i = -42;
  //@ integer_to_chars(&x.i);
  
  //@ chars_to_u_integer(&x.i);
  x.u = 42;
  //@ u_integer_to_chars(&x.i);
  
  return 0;
}


