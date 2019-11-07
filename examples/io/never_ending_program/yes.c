/**
 * yes.c - prints "y\n" forever.
 *
 * This program keeps running forever.
 * (in the physical world: until the computer shuts down, if ever)
 */

#include <stdio_simple.h>
//#include <stdio.h> // useful for compiling.


/*@
// This expresses an action that never terminates.
copredicate yes_io(place t1) =
  write_char_io(t1, stdout, 'y', _, ?t2)
  &*& write_char_io(t2, stdout, '\n', _, ?t3)
  &*& yes_io(t3);
@*/

int main() //@ : custom_main_spec
//@ requires token(?t1) &*& yes_io(t1);
//@ ensures false; // does not terminate.
{
  int counter = 0;
  while (1)
    //@ invariant token(?t) &*& yes_io(t);
  {
    //@ open yes_io(t);
    putchar('y');
    putchar('\n');
  }

}
