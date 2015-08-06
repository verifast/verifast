/**
 * tee.c - minimalistic example of compositional I/O with buffering.
 *
 * This program reads from stdin, and writes its input to both stdout and stderr.
 * The specifications allow buffering of any size.
 * To illustrate this, the implementation buffers 2 bytes
 * (i.e. reads 2 bytes, then writes 2, then reads 2, etc).
 *
 * This implementation is recursive (instead of a while loop).
 */

#include <stdio_simple.h>
// #include <stdio.h>

#include "tee_buffered.h"


void tee()
/*@ requires read_till_eof_io(?t_read1, ?contents, ?t_read2) &*& token(t_read1)
         &*& tee_out_string_io(?t_write1, contents, ?t_write2) &*& token(t_write1);
@*/	
//@ ensures token(t_read2) &*& token(t_write2);
{
  //@ open read_till_eof_io(_, _, _);
  int c1 = getchar();
  if (c1 >= 0){
    //@ open read_till_eof_io(_, _, _);
    int c2 = getchar();
    //@ open tee_out_string_io(_, _, _);
    tee_out(c1);
    if (c2 >= 0){
      //@ open tee_out_string_io(_, _, _);
      tee_out(c2);
      tee();
    }
    /*@
    if (c2 < 0){
      open tee_out_string_io(_, _, _);
      no_op();
    }
    @*/
  }
  /*@
  if (c1 < 0){
    open tee_out_string_io(_, _, _);
    no_op();
  }
  @*/
}

int main(int argc, char **argv) //@ : main_io(tee_buffered_recursive)
/*@ requires module(tee_buffered_recursive, true)
  &*& [_]argv(argv, argc, ?arguments)
  &*& main_io(?t1, arguments, ?t2)
  &*& token(t1);
@*/
/*@ ensures token(t2);
@*/
{
  //@ open main_io(_, _, _);
  //@ open tee_buffered_io(_, _, _);
  //@ split();
  tee();
  //@ join();
  return 0;
//@ leak module(_, _);
}
