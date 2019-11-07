#include <stdio_simple.h>

/*@ predicate example_io(place t1; place t3) =
  write_char_io(t1, stdout, 'h', _, ?t2)
  &*& write_char_io(t2, stdout, 'i', _, t3);
@*/

typedef void main_spec();
//@ requires token(?t1) &*& example_io(t1, ?t2);
//@ ensures token(t2);

