/**
 * Consider the following grammar: 
 *   brackets = '(' brackets ')' brackets | epsilon
 * Here, epsilon denotes the empty string.
 *
 * The contract of this file says the program is allowed
 * to output any string of the language of this grammar.
 */
#include <stdio_simple.h>

//@ #include <bigstar.gh>

/*@
// Expresses the following grammar:   brackets = '(' brackets ')' brackets | epsilon
predicate matching_brackets_helper(time t1, list<bool> choices, time t2) =
  t1 == t2 ?
    choices == {false}
  :
    write_char_io(t1, stdout, '(', _, ?t_open)
    &*& matching_brackets_helper(t_open, ?subchoices1, ?t_center)
    &*& write_char_io(t_center, stdout, ')', _, ?t_close)
    &*& matching_brackets_helper(t_close, ?subchoices2, t2)
    &*& choices == cons(true, append(subchoices1, subchoices2))
;

// Make it a predicate with one argument because bigstar expects the predicate to have one argument.
predicate_ctor matching_brackets_ctor(time t1, time t2)(list<bool> choices) =
  matching_brackets_helper(t1, choices, t2);
@*/


void main()
//@ requires time(?t1) &*& exists<time>(?t2) &*& bigstar<list<bool> >(matching_brackets_ctor(t1, t2), nil);
//@ ensures time(t2);
{
  //@ bigstar_extract(matching_brackets_ctor(t1, t2), {true, false, false});
  //@ open matching_brackets_ctor(t1,t2)(_);
  //@ open matching_brackets_helper(_, _, _);
  //@ assert write_char_io(t1, _, '(', _, ?t_open); // bind t_open
  //@ open matching_brackets_helper(t_open, _, _); // open this one first.
  //@ open matching_brackets_helper(_, _, _);
  putchar('(');
  putchar(')');
  //@ leak bigstar(_, _);
}
