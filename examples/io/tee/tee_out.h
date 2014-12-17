/**
 * tee_out - writes to both stdout and stderr.
 * This demonstrates i/o compositionality: we made an i/o operation (tee_out)
 * on top of other i/o operations (write_char_io). On top of tee_out you can
 * then define other i/o operations (see e.g. tee.c).
 */

#ifndef TEE_OUT_H
#define TEE_OUT_H

#include <stdio_simple.h>
// #include <stdio.h>


/*@
predicate tee_out_io(place t1, unsigned char c; place t2) =
  c >= 0 && c <= 255
  &*& split(t1, ?t_stdout1, ?t_stderr1)
    &*& write_char_io(t_stdout1, get_stdout(), c, ?success_stdout, ?t_stdout2)
    //---
    &*& write_char_io(t_stderr1, get_stderr(), c, ?success_stderr, ?t_stderr2)
  &*& join(t_stdout2, t_stderr2, t2);
@*/

void tee_out(int c);
//@ requires tee_out_io(?t1, c, ?t2) &*& token(t1);
//@ ensures token(t2);



#endif

