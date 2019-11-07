/**
 * Reads a string and outputs whether it is a string of the mathing brackets grammar.
 *
 * Consider the grammar of matching brackets: B ::= `(' B `)' B | emptystring
 * If the string that is read is of the language defined by the grammer, then print `1'.
 * If it is not, print `0'.
 *
 */

//#include <stdio.h>
#include <stdio_simple.h>
//@ #include <io.gh>
#include <malloc.h>
#include <stdlib.h> // abort() (used when malloc fails)


int *c;
//@ predicate buffer(int *cc, int ccc) = pointer(&c, cc) &*& integer(cc, ccc);

int pop_read_ahead()
//@ requires buffer(?cc, ?c_old) &*& token(?t1) &*& read_char_io(t1, stdin, ?new_char, ?success, ?t2);
//@ ensures buffer(cc, new_char) &*& token(t2) &*& result == c_old;
{
  //@ open buffer(_, _);
  int c_copy = *c;
  int c_new = getchar();
  *c = c_new;
  //@ assert c_new == new_char;
  //@ close buffer(cc, new_char);
  return c_copy;
}

int peek_read_ahead()
//@ requires [?f]buffer(?cc, ?ccc);
//@ ensures [f]buffer(cc, ccc) &*& result == ccc;
{
  //@ open [f]buffer(cc, ccc);
  return *c;
  //@ close [f]buffer(cc, ccc);
}

/*@
predicate brackets_io(place t_read1, int read1, int read5, bool valid, place t_read5) =

  //        (   brackets   )   brackets
  // read:  1   2          3   4          5

  read1 == '(' ?
    read_char_io(t_read1, stdin, ?read2, _, ?t_read2) // for sub brackets
    &*& brackets_io(t_read2, read2, ?read3, ?subvalid1, ?t_read3)
    &*& read_char_io(t_read3, stdin, ?read4, _, ?t_read4)
    &*& brackets_io(t_read4, read4, read5, ?subvalid2, t_read5)
    &*& valid == (subvalid1 && read3 == ')' && subvalid2)
  :
   no_op(t_read1, t_read5) &*& read5 == read1
   &*& valid == (read1 < 0 || read1 == ')');
@*/


bool brackets()
/*@ requires
  buffer(?cc, ?read1) // contains the read ahead
  &*& brackets_io(?t_read1, read1, ?read5, ?valid, ?t_read5)
  &*& token(t_read1);
@*/
//@ ensures buffer(cc, read5) &*& token(t_read5) &*& result == valid;
{
  //@ open brackets_io(_, _, _, _, _);
  if (peek_read_ahead() == '('){
    pop_read_ahead();
    bool brackets1 = brackets();
    bool should_be_close = (pop_read_ahead() == ')');
    bool brackets2 = brackets();
    return brackets1 && should_be_close && brackets2;
  } else{
     int i = peek_read_ahead();
     //@ no_op();
     if (i < 0){
      return true;  // empty string because read eof
    } else if (peek_read_ahead() == ')'){
      return true;  // match empty string because read ')'
    } else {
      return false; // no match because read invalid character
    }
  }
}

int main() //@ : custom_main_spec
/*@ requires token(?t1)
  &*& read_char_io(t1, stdin, ?read_ahead, _, ?t_read_ahead)
  &*& brackets_io(t_read_ahead, read_ahead, ?read_last, ?valid, ?t_brackets_end)
  &*& read_last < 0 // must read till EOF
  &*& write_char_io(t_brackets_end, stdout, (valid ? '1' : '0'), _, ?t_end)
  &*& module(matching_brackets_checker, true);
@*/
//@ ensures token(t_end) &*& module(matching_brackets_checker, _);
{
  //@ open_module();
  c = malloc(sizeof(int));
  if (c == 0){
    abort();
  }
  
  // Split in two lines because otherwise we have the erro
  // "This potentially side-effecting expression is not supported in this position,
  //  because of C's unspecified evaluation order".
  int c_local = getchar();
  *c = c_local;
  
  //@ close buffer(c, c_local);
  bool match = brackets();
  if (match == true){
    putchar ('1');
  }else{
    putchar ('0');
  }
  //@ open buffer(_, _);
  free(c);
  //@ close_module();

  return 0;
}
