/**
 * Program that prints 1,2,3,4,... in unary notation
 * and never stops.
 * (because a computer has finite memory it is impossible to implement
 * this, but the contract is written as such. The current implementation
 * counts until UINT_MAX and then aborts).
 *
 * This is an example of I/O verification of nonterminating
 * programs. It uses a coinductive predicate.
 */

#include <stdio_simple.h>
//#include <stdio.h>
#include <stdbool.h>
#include <limits.h>

#include <stdlib.h>

/*@

predicate print_unary_io(place t1, int number, place t_end) =
  number >= 1 ?
    write_char_io(t1, stdout, '1', _, ?t2)
    &*& print_unary_io(t2, number - 1, t_end)
  :
    no_op(t1, t_end);

copredicate infinite_counter_io(place t1, int number, place t_end) =
  print_unary_io(t1, number, ?t2)
  &*& write_char_io(t2, stdout, '\n', _, ?t3)
  &*& infinite_counter_io(t3, number + 1, t_end);
@*/

int main() //@ : custom_main_spec
//@ requires token(?t1) &*& infinite_counter_io(t1, 0, ?t_end);
//@ ensures false; // program must not terminate.
{
  unsigned int count = 0;
  while(true)
    //@ invariant token(?t_cur) &*& infinite_counter_io(t_cur, count, t_end);
  {
    unsigned int unary_count = 0;
    //@ open infinite_counter_io(_, _, _);
    //@ assert print_unary_io(_, _, ?t_unary_end);
    while (unary_count < count)
      /*@ invariant
        token(?t1_unary) &*& print_unary_io(t1_unary, count - unary_count, t_unary_end);
      @*/
    {
      //@ open print_unary_io(_, _, _);
      putchar('1');
      unsigned char u = 0;
      
      // VeriFast does not support "unary_count++;" for unsigned int.
      unary_count = unary_count + ((unsigned int) 1);
    }
    //@ open print_unary_io(_, _, _);
    //@ no_op();
    putchar('\n');
    if (count == UINT_MAX){
      abort(); // use bigint if you want more.
    }
    count = count + ((unsigned int) 1);
  }
}
