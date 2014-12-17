/**
 * tee.c - minimalistic example of compositional I/O with buffering.
 *
 * This program reads from stdin, and writes its input to both stdout and stderr.
 * The specifications allow buffering of any size.
 * To illustrate this, the implementation buffers 2 bytes
 * (i.e. reads 2 bytes, then writes 2, then reads 2, etc).
 */

#include <stdio_simple.h>
// #include <stdio.h>

#include "tee_out.h"


/*@
predicate read_till_eof_io(place t1; list<char> contents, place t2) =
  read_char_io(t1, stdin, ?c, ?success, ?t_read)
  &*& success ?
    read_till_eof_io(t_read, ?sub, t2)
    &*& contents == cons(c, sub)
  :
    t2 == t_read
    &*& contents == nil;
@*/

/*@
predicate tee_out_string_io(place t1, list<char> contents; place t2) =
  contents == nil ?
    t2 == t1
  :
    tee_out_io(t1, head(contents), ?t_read)
    &*& tee_out_string_io(t_read, tail(contents), t2);
@*/

/*@
predicate tee_buffered_io(place t1, list<char> contents; place t2) =
  split(t1, ?t_read1, ?t_write1)
    &*& read_till_eof_io(t_read1, contents, ?t_read2)
    // --
    &*& tee_out_string_io(t_write1, contents, ?t_write2)
  &*& join(t_read2, t_write2, t2);
  
predicate main_io(place t1, list<list<char> > arguments, place t2) =
  tee_buffered_io(t1, _, t2);
@*/


int main(int argc, char **argv) //@ : main_io(tee_buffered)
/*@ requires module(tee_buffered, true)
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
      join();
    }
    @*/
  }
  return 0;
//@ leak module(_, _);
}
