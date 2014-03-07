/**
 * tee.c - minimalistic example of compositional I/O.
 *
 * This program reads from stdin, and writes its input to both stdout and stderr.
 */

//@ #include <io.gh>
#include <stdio_simple.h>
// #include <stdio.h>
// #define get_stderr() stderr

/*@		
predicate tee_out_io(time t1, unsigned char c; time t2) =
  c >= 0 && c <= 255
  &*& split(t1, ?t_stdout1, ?t_stderr1)
    &*& write_char_io(t_stdout1, stdout(), c, ?success_stdout, ?t_stdout2)
    //---
    &*& write_char_io(t_stderr1, stderr(), c, ?success_stderr, ?t_stderr2)
  &*& join(t_stdout2, t_stderr2, t2);
@*/

void tee_out(int c)
//@ requires tee_out_io(?t1, c, ?t2) &*& time(t1);
//@ ensures time(t2);
{
  //@ open tee_out_io(_, _, _);
  //@ split();
  putchar(c);
  putc(c, get_stderr());
  //@ join();
}


/*@
predicate tee_io(time t1, list<char> contents; time t2) =
  read_char_io(t1, stdin(), ?c, ?success, ?t_read)
  &*& success ?
    length(contents) > 0
    &*& head(contents) == c
    &*& c >= 0 && c <= 255
    &*& tee_out_io(t_read, c, ?t_out)
    &*& tee_io(t_out, tail(contents), t2) 
  :
    contents == nil
    &*& t2 == t_read;
  
predicate main_io(time t1, list<list<char> > arguments, time t2) =
  tee_io(t1, _, t2);
@*/


int main(int argc, char **argv) //@ : main_io(tee)
/*@ requires module(tee, true)
  &*& [_]argv(argv, argc, ?arguments)
  &*& main_io(?t1, arguments, ?t2)
  &*& time(t1);
@*/
/*@ ensures time(t2);
@*/
{
  //@ open main_io(_, _, _);
  int c = 0;
  while (c >= 0)
    /*@ invariant
      c >= 0 ?
        tee_io(?t_tee1, ?contents, t2) &*& time(t_tee1)
      :
        time(t2)
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
