/**
 * hello-world.c: very basic I/O verification example
 * of a program that prints "hi".
 */

#include <stdio_simple.h>
//#include <stdio.h>

int main() //@ : custom_main_spec
/*@ requires token(?t1)
  &*& write_char_io(t1, stdout, 'h', _, ?t2)
  &*& write_char_io(t2, stdout, 'i', _, ?t3);
@*/
//@ ensures token(t3);
{
  putchar('h');
  putchar('i');

  return 0;
}
