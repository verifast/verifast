/**
 * First read turing_complete.c and turing_complete_lowtech.c.
 *
 * This example uses a non-deterministic turing machine. This allows
 * you to write underspecified specifications: "the program is allowed
 * to do X or Y". The implementation of the program can choose whether it does X or Y.
 *
 * One might expect a different approach: instead of using non-deterministic
 * turing machines, one could consider the approach where the specifications are
 * of the form "the program is allowed to do any actions of which the
 * encoding is accepted by the turing machine". A turing machine accepts
 * its input (i.e. the encoding of I/O actions) if it terminates and
 * upon termination, is in a state that is in the set of final/accepting states.
 * This makes it harder to deal with non-terminating programs that do
 * an infinite number of I/O actions. The turing machine should in finite time
 * go into an accepting state for an infinite number of I/O actions. This is undesired.
 * With the approach used in this file, using non-deterministic turing machines,
 * infinite number of I/O actions for non-terminating programs is straightforward.
 */

//@#include <io.gh>
#include <stdio_simple.h>

/*@
copredicate tm_transition_io(place t1, list<int> tm, int _action, int write_value, int new_state, list<int> tape_left, list<int> tape_right, place t2) =
  _action == 0 ? // do not move
    tm_io(t1, tm, new_state, tape_left, tape_right, t2)
  : _action == -1 ?  // move left
    tm_io(t1, tm, new_state, tail(tape_left), cons(write_value, tape_right), t2)
  : _action == 1 ?   // move right
    tm_io(t1, tm, new_state, cons(write_value, tape_left), tail(tape_right), t2)
  : _action == 2 ?   // read i/o
    read_char_io(t1, stdin, ?read_value, ?success, ?t_before)
    &*& tm_io(t_before, tm, new_state, tape_left, cons(read_value, tail(tape_right)), t2)
  : _action == 3 ?   // write i/o
    write_char_io(t1, stdout, write_value, ?success, ?t_before)
    &*& tm_io(t_before, tm, new_state, tape_left, tape_right, t2)
  : // unknown action, does not happen for proper encoded turing machines
    exists<list<int> >({'B','A','D','_','T', 'M'})
;

copredicate tm_lookup_io(place t1, list<int> tm, list<int> tm_unwinding, bool line_found, int state, list<int> tape_left, list<int> tape_right, place t2) =
  tm_unwinding == nil? // All possible transitions are already considered
    line_found ? // There was at least one transition, i.e. the TM did not halt
      emp
    :
      no_op(t1, t2) // No transition in TM. Halt.
  :
    // Take the table of the transitions with the first row removed
    [_]exists<list<int> >(?tm_smaller) &*& tm_smaller == tail(tail(tail(tail(tail(tm_unwinding)))))
    
    // Consider the first transition in the list of transitions encoded in tm_unwinding.
    &*& head(tm_unwinding) == state && head(tail(tm_unwinding)) == head(tape_right) ? // transition is for correct state&symbol
    
      // We know tm_unwinding's first transition is one that can fire,
      // also look at the other transitions:
      tm_lookup_io(t1, tm, tm_smaller, true, state, tape_left, tape_right, t2)
      
      // Decode tm_unwinding's first transition:
      &*& [_]exists<int>(?_action) &*& _action == head(tail(tail(tm_unwinding)))
      &*& [_]exists<int>(?write_value) &*& write_value == head(tail(tail(tail(tm_unwinding))))
      &*& [_]exists<int>(?new_state) &*& new_state == head(tail(tail(tail(tail(tm_unwinding)))))
      
      // Fire the transition
      &*& tm_transition_io(t1, tm, _action, write_value, new_state, tape_left, tape_right, t2)
      
    : // The transition was for wrong state/symbol, let's continiue searching transitions
      tm_lookup_io(t1, tm, tm_smaller, line_found, state, tape_left, tape_right, t2)
;

/**
 * Represents the permission to do the input output actions which the given tm does.
 */
// It is easier in proofs to separate tm_lookup_io from tm_io. Technically it's the same but conceptually it's a bit different
copredicate tm_io(place t1, list<int> tm, int state, list<int> tape_left, list<int> tape_right, place t2) =
  tm_lookup_io(t1, tm, tm, false, state, tape_left, tape_right, t2);


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
  &*& tm_io(t1, ?tm, 0, {}, {}, ?t2)
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
        tm_io(t1_loop, tm, 0, {}, ?tape_right, t2)
        &*& tape_right == nil || tape_right == {c}
      :
        no_op(t1_loop, t2);
    @*/
  {
    //@ open tm_io(_, _, _, _, ?tape_right, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ open tm_transition_io(_, _, _, _, _, _, _, _);
    c = getchar();
    
    //@ open tm_io(_, _, _, _, _, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ open tm_lookup_io(_, _, _, _, _, _, _, _);
    //@ if (c == 'a' || c == 'b') open tm_transition_io(_, _, _, _, _, _, _, _);
    
    if (c == 'a' || c == 'b'){
      putchar(c);
    }
  }
  //@ no_op();
}



