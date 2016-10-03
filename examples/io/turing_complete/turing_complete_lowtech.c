/**
 * Read turing_complete.c first to know what this is about.
 *
 * This example is similar, but it restricts the programming and
 * verification language constructs we are allowed to use.
 * While turing-machine.c uses fixpoints, inductive data types,
 * lists of lists, and the assoc function, this example only uses the
 * constructs you expect from a paper formalization.
 *
 * We encode a turing machine as a list of integers. It represents the
 * serialization of the table form of the transition function.
 * The list is of the form: {state, on_tape, action, write, new_state,
 *                           state, on_tape, action, write, new_state,
 *                           ... }
 * This represents the function: if the turing machine is on state
 * <state> with <on_tape> at the tape's head position, it will perform
 * action <action> and go into state <new_state>.
 * Actions are encoded as follows:
 * <action>=0 : do not move the tape.
 * <action>=-1: write <write> to tape, and move tape left
 * <action>=1 : write <write> to tape, and move tape right 
 * <action>=2 : read from standard input, and write the read value to
 *              the tape (ignore write field)
 * <action>=3 : write the value currently under the tape's head to
 *              standard output
 */

//@#include <io.gh>
#include <stdio_simple.h>

/*@
copredicate tm_lowtech_lookup(list<int> tm, int state, int on_tape, int _action, int write_value, int new_state) =
  tm == nil?
    _action == 4 // encoding of "halt".
  :
    head(tm) == state ?
      head(tail(tm)) == on_tape ?
        _action == head(tail(tail(tm)))
        &*& write_value == head(tail(tail(tail(tm))))
        &*& new_state == head(tail(tail(tail(tail(tm)))))
     :
       tm_lowtech_lookup(tail(tail(tail(tail(tail(tm))))), state, on_tape, _action, write_value, new_state)
   :
     tm_lowtech_lookup(tail(tail(tail(tail(tail(tm))))), state, on_tape, _action, write_value, new_state)
;
copredicate tm_lowtech_io(place t1, list<int> tm, int cur_state, list<int> tape_left, list<int> tape_cur_and_right, place t2) =
  tm_lowtech_lookup(tm, cur_state, head(tape_cur_and_right), ?_action, ?write_value, ?new_state)
  &*& _action == 0 ? // do not move
    tm_lowtech_io(t1, tm, new_state, tape_left, tape_cur_and_right, t2)
  : _action == -1 ?  // move left
    tm_lowtech_io(t1, tm, new_state, tail(tape_left), cons(write_value, tape_cur_and_right), t2)
  : _action == 1 ?   // move right
    tm_lowtech_io(t1, tm, new_state, cons(write_value, tape_left), tail(tape_cur_and_right), t2)
  : _action == 2 ?   // read i/o
    read_char_io(t1, stdin, ?read_value, ?success, ?t_before)
    &*& tm_lowtech_io(t_before, tm, new_state, tape_left, cons(read_value, tail(tape_cur_and_right)), t2)
  : _action == 3 ?   // write i/o
    write_char_io(t1, stdout, write_value, ?success, ?t_before)
    &*& tm_lowtech_io(t_before, tm, new_state, tape_left, tape_cur_and_right, t2)
  : _action == 4 ?   // halt (encoded in TM as no transition)
    no_op(t1, t2)
  : // does not happen for proper encoded turing machines
    emp
;
@*/


// -------------------------------------------------------------- \\
//           Example: a (trivial) turing machine: "cat"           \\
// -------------------------------------------------------------- \\

/**
 * This program writes to stdout what it reads from stdin.
 * 
 * To keep the example small, the program stops if it reads
 * a character different from 'a' and 'b', but it is
 * easy to add more characters.
 */
void cat()
/*@ requires token(?t1)
  &*& tm_lowtech_io(t1, ?tm, 0, {}, {}, ?t2)
  // columns: state, on_tape, action, write, new_state
  &*& tm == { 0    , 0      , 2     , -1   , 1, // because tape is initially empty.
              0    , 'a'    , 2     , -1   , 1,
              0    , 'b'    , 2     , -1   , 1,
              1    , 'a'    , 3     , 'a'  , 0,
              1    , 'b'    , 3     , 'b'  , 0
  };
@*/
//@ ensures token(t2);
{
  int c = 'a';
  while(c == 'a' || c == 'b')
    /*@ invariant token(?t1_loop) &*&
      c == 'a' || c == 'b' ?
        tm_lowtech_io(t1_loop, tm, 0, {}, ?tape_right, t2)
        &*& tape_right == nil || tape_right == {97} || tape_right == {98}
      :
        no_op(t1_loop, t2);
    @*/
  {
    //@ open tm_lowtech_io(_, _, _, _, ?tape_right, _);
    //@ open tm_lowtech_lookup(_, _, _, _, _, _);
    //@ if (head(tape_right) >= 97) open tm_lowtech_lookup(_, _, _, _, _, _);
    //@ if (head(tape_right) == 98) open tm_lowtech_lookup(_, _, _, _, _, _);
    c = getchar();
    //@ open tm_lowtech_io(_, _, _, _, _, _);
    //@ open tm_lowtech_lookup(_, _, _, _, _, _);
    //@ open tm_lowtech_lookup(_, _, _, _, _, _);
    //@ open tm_lowtech_lookup(_, _, _, _, _, _);
    //@ open tm_lowtech_lookup(_, _, _, _, _, _);
    //@ if (c != 'a') open tm_lowtech_lookup(_, _, _, _, _, _);
    //@ if (c != 'a' && c != 'b') open tm_lowtech_lookup(_, _, _, _, _, _);
    if (c == 'a' || c == 'b'){
      putchar(c);
    }
  }
  //@ no_op();
}



