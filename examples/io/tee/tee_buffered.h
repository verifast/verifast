#ifndef TEE_BUFFERED_H
#define TEE_BUFFERED_H

#include <stdio_simple.h>
#include "tee_out.h"

/*@
predicate read_till_eof_io(place t1; list<char> contents, place t2) =
  read_char_io(t1, stdin, ?c, ?success, ?t_read)
  &*& success ?
    read_till_eof_io(t_read, ?sub, t2)
    &*& contents == cons(c, sub)
  :
    t2 == t_read &*& contents == nil;
@*/

/*@
predicate tee_out_string_io(place t1, list<char> contents, place t2;) =
  contents == nil ?
    // It's also possible to write "t2==t1" here,
    // but it is better to write "no_op(t1, t2)".
    // See the documentation of no_op in io.gh for more info.
    no_op(t1, t2)
  :
    tee_out_io(t1, head(contents), ?t_read)
    &*& tee_out_string_io(t_read, tail(contents), t2);
@*/

/*@
predicate tee_buffered_io(place t1, list<char> contents, place t2) =
  split(t1, ?t_read1, ?t_write1)
    &*& read_till_eof_io(t_read1, contents, ?t_read2)
    // --
    &*& tee_out_string_io(t_write1, contents, ?t_write2)
  &*& join(t_read2, t_write2, t2);
  
predicate main_io(place t1, list<list<char> > arguments, place t2) =
  tee_buffered_io(t1, _, t2);
@*/

#endif
