/**
 * See tee_out.h
 */
#include "tee_out.h"

void tee_out(int c)
//@ requires tee_out_io(?t1, c, ?t2) &*& token(t1);
//@ ensures token(t2);
{
  //@ open tee_out_io(_, _, _);
  //@ split();
  putchar(c);
  putc(c, get_stderr());
  //@ join();
}
