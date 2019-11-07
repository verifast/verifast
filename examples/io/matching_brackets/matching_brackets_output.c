/**
 * Consider the following grammar: 
 *   brackets = '(' brackets ')' brackets | epsilon
 * Here, epsilon denotes the empty string.
 *
 * The contract of this file says the program is allowed
 * to output any string of the language of this grammar.
 */
#include <stdio_simple.h>

/*@
/* We have two copredicates (matching_brackets and matching_brackets_helper)
 * because it makes it easier to deal with leaking unused permissions.
 * If you prefere to only use one copredicate, this is possible as well.
 * It is also possible to use one copredicate for the contract,
 * and convert it to two copredicates (using a lemma) for verification.
 */
copredicate matching_brackets_helper(place t1, place t2) =
  write_char_io(t1, stdout, '(', _, ?t_open)
  &*& matching_brackets(t_open, ?t_center)
  &*& write_char_io(t_center, stdout, ')', _, ?t_close)
  &*& matching_brackets(t_close, t2);

// Expresses the following grammar:   brackets = '(' brackets ')' brackets | epsilon
copredicate matching_brackets(place t1, place t2) =
  no_op(t1, t2) // epsilon
  &*& matching_brackets_helper(t1, t2);
@*/

int main() //@ : custom_main_spec
//@ requires token(?t1) &*& matching_brackets(t1, ?t2);
//@ ensures token(t2);
{
  //@ open matching_brackets(t1, t2);
  //@ leak no_op(_, _);
  //@ open matching_brackets_helper(t1, t2);
  //@ assert write_char_io(t1, _, '(', _, ?t_open); // bind t_open
  putchar('(');
  //@ open matching_brackets(t_open, ?t_center);
  //@ leak matching_brackets_helper(t_open, t_center);
  //@ no_op();
  putchar(')');
  //@ open matching_brackets(?t_close, t2);
  //@ no_op();
  //@ leak matching_brackets_helper(t_close, t2);
  
  return 0;
}
