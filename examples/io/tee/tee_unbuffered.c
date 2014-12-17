/**
 * tee.c - minimalistic example of compositional I/O.
 *
 * This program reads from stdin, and writes its input to both stdout and stderr.
 *
 * The specifications forbid buffering, see tee_buffered.c for a buffered example.
 */

//@ #include <io.gh>
#include <stdio_simple.h>
// #include <stdio.h>

#include "tee_out.h"

/*@
predicate tee_io(place t1, list<char> contents; place t2) =
  read_char_io(t1, stdin, ?c, ?success, ?t_read)
  &*& success ?
    length(contents) > 0
    &*& head(contents) == c
    &*& c >= 0 && c <= 255
    &*& tee_out_io(t_read, c, ?t_out)
    &*& tee_io(t_out, tail(contents), t2) 
  :
    contents == nil
    &*& t2 == t_read;
  
predicate main_io(place t1, list<list<char> > arguments, place t2) =
  tee_io(t1, _, t2);
@*/


int main(int argc, char **argv) //@ : main_io(tee_unbuffered)
/*@ requires module(tee_unbuffered, true)
  &*& [_]argv(argv, argc, ?arguments)
  &*& main_io(?t1, arguments, ?t2)
  &*& token(t1);
@*/
/*@ ensures token(t2);
@*/
{
  //@ open main_io(_, _, _);
  int c = 0;
  while (c >= 0)
    /*@ invariant
      c >= 0 ?
        tee_io(?t_tee1, ?contents, t2) &*& token(t_tee1)
      :
        token(t2)
      ;
    @*/
  {
    //@ open tee_io(_, _, _);
    c = getchar();
    if (c >= 0){
      tee_out(c);
    }
  }
  return 0;
//@ leak module(_, _);
}
