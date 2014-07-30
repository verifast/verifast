#include <stdio_simple.h>

/*@ predicate example_io(time t1; time t3) =
  write_char_io(t1, stdout, 'h', _, ?t2)
  &*& write_char_io(t2, stdout, 'i', _, t3);
@*/

void main();
//@ requires time(?t1) &*& example_io(t1, ?t2);
//@ ensures time(t2);

