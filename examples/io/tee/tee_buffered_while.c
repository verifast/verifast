/**
 * tee.c - minimalistic example of compositional I/O with buffering.
 *
 * This program reads from stdin, and writes its input to both stdout and stderr.
 * The specifications allow buffering of any size.
 * To illustrate this, the implementation buffers 2 bytes
 * (i.e. reads 2 bytes, then writes 2, then reads 2, etc).
 *
 * This implementation uses a while loop (instead of recursion).
 */

#include <stdio_simple.h>
// #include <stdio.h>

#include "tee_buffered.h"


int main(int argc, char **argv) //@ : main_io(tee_buffered_while)
/*@ requires module(tee_buffered_while, true)
  &*& [_]argv(argv, argc, ?arguments)
  &*& main_io(?t1, arguments, ?t2)
  &*& token(t1);
@*/
/*@ ensures token(t2);
@*/
{
  //@ open main_io(_, _, _);
  int c1 = 0;
  int c2 = 0;
  //@ open tee_buffered_io(t1, _, t2);
  //@ split();
  while (c2 >= 0)
    /*@ invariant
      c2 >= 0 ?
        read_till_eof_io(?t_read1, ?contents, ?t_read2) &*& token(t_read1)
        &*& tee_out_string_io(?t_write1, contents, ?t_write2) &*& token(t_write1)
        &*& join(t_read2, t_write2, t2)
      :
        token(t2)
      ;
    @*/
  {
    //@ open read_till_eof_io(_, _, _);
    //@ open tee_out_string_io(_, _, _);
    c1 = getchar();
    if (c1 >= 0){
      //@ open read_till_eof_io(_, _, _);
      //@ open tee_out_string_io(_, _, _);
      c2 = getchar();
      
      // Now write output:
      tee_out(c1);
      if (c2 >= 0){
        tee_out(c2);
      }
    }else{
      c2 = -1;
    }
    /*@
    if (c2 < 0){
      no_op();
      join();
    }
    @*/
  }
  return 0;
//@ leak module(_, _);
}
