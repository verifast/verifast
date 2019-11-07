/**
 * Consider the following grammar: 
 *   brackets = '(' brackets ')' brackets | epsilon
 * Here, epsilon denotes the empty string.
 *
 * This program is a program that crashes if the input is not consistent with the grammar.
 * The prove proves that, on correct input, the program does not crash.
 */
#include <stdio_simple.h>



/*@
// Expresses the following grammar:   brackets = '(' brackets ')' brackets | epsilon
predicate matching_brackets_helper(place t1, place t2) =
  t1 == t2 ?
    emp
  :
    read_char_io(t1, stdin, '(', true, ?t_open)
    &*& matching_brackets_helper(t_open, ?t_center)
    &*& read_char_io(t_center, stdin, ')', true, ?t_close)
    &*& matching_brackets_helper(t_close, t2);
@*/


int main() //@ : custom_main_spec
/*@ requires token(?t1) &*& matching_brackets_helper(t1, ?t_help)
  &*& read_char_io(t_help, stdin, _, false, ?t2); // end of file
@*/
//@ ensures token(t2);
{
  
  int counter = 0;
  int c;
  //@ brackets_to_iterative(t1);
  do
    /*@ invariant
      token(?t1_)
      &*& matching_brackets_iterative(t1_, counter, ?depth, t_help)
      &*& counter >= 0
      &*& read_char_io(t_help, stdin, _, false, t2);
    @*/
  {
    //@ open matching_brackets_iterative(t1_, counter, depth, t_help);
    c = getchar();
    if (c == '('){
      counter ++;
    }else if (c == ')'){
      counter --;
    }
    if (counter < 0){
      //@ open matching_brackets_iterative(?arg1, ?arg2, ?arg3, ?arg4);
      //@ close matching_brackets_iterative(arg1, arg2, arg3, arg4);
      int *nullptr = 0;
      // allowed to crash (the verifier proves this never happens if function's precondition satisfied)
      *nullptr = 0;
    }
  } while (c >= 0);
  if (counter > 0){
    int *nullptr = 0;
    // allowed to crash (the verifier proves this never happens if function's precondition satisfied)
    *nullptr = 0;
  }

  return 0;
}


/* To prove the program, we transform the predicate matching_brackets_helper
 * that looks like a grammar to the predicate matching_brackets_iterative
 * that is closer to the way the program works.
 *
 * The lemmas below do this transformation.
 */

/*@
predicate matching_brackets_iterative(place t1, int depth, int length, place t2) =
  depth >= 0
  &*& length >= 0
  &*& length == 0 ?
    t1 == t2
    &*& depth == 0
  :
    read_char_io(t1, stdin, ?c, true, ?t_start)
    &*& matching_brackets_iterative(t_start, ?sub_depth,length - 1, t2)
    &*& c == '(' ?
      sub_depth == depth + 1
   :
      c == ')'
      &*& sub_depth == depth - 1
;

lemma void brackets_iterative_add_close(place t_open)
requires matching_brackets_iterative(t_open, ?depth, ?length, ?t_center)
    &*& read_char_io(t_center, stdin, ')', true, ?t_close);
ensures matching_brackets_iterative(t_open, depth + 1, length + 1, t_close);
{
  if (length == 0){
    open matching_brackets_iterative(_, _, _, _);
    close matching_brackets_iterative(t_close, 0, 0, t_close);
    close matching_brackets_iterative(t_open, 1, 1, t_close);
  }else{
    open matching_brackets_iterative(_, _, _, _);
    assert matching_brackets_iterative(?t_sub, _, _, _);
    brackets_iterative_add_close(t_sub);
    close matching_brackets_iterative(t_open, depth + 1, length + 1, t_close);
  }
}

lemma void brackets_iterative_deepen(place t1)
requires read_char_io(t1, stdin, '(', true, ?t_open)
    &*& matching_brackets_iterative(t_open, 0, ?length, ?t_center)
    &*& read_char_io(t_center, stdin, ')', true, ?t_close);
ensures matching_brackets_iterative(t1, 0, length + 2, t_close);
{
  // to obtain length >= 0 
  open  matching_brackets_iterative(t_open, 0, length, t_center);
  close matching_brackets_iterative(t_open, 0, length, t_center);
  
  brackets_iterative_add_close(t_open);
  close matching_brackets_iterative(t1, 0, length + 2, t_close);
}

lemma void brackets_iterative_concat(place t1)
requires matching_brackets_iterative(t1, ?depth, ?length1, ?t2)
  &*& matching_brackets_iterative(t2, 0, ?length2, ?t3);
ensures matching_brackets_iterative(t1, depth, length1 + length2, t3);
{
  open matching_brackets_iterative(t1, depth, length1, t2);
  if (length1 != 0){
    assert matching_brackets_iterative(?t_start, _, length1 - 1, t2);
    brackets_iterative_concat(t_start);
    
    assert matching_brackets_iterative(t_start, ?subdepth, length1 + length2 - 1, t3); // result of recursive call
    
    // to show length1 + length2 - 1 >= 0
    open matching_brackets_iterative(t_start, subdepth, length1 + length2 - 1, t3);
    close matching_brackets_iterative(t_start, subdepth, length1 + length2 - 1, t3);
    
    close matching_brackets_iterative(t1, depth, length1 + length2, t3);
  }
}

lemma void brackets_to_iterative(place t1)
    requires matching_brackets_helper(t1, ?t2);
    ensures matching_brackets_iterative(t1, 0, _, t2);
{
  open matching_brackets_helper(t1, t2);
  if (t1 == t2){
    close matching_brackets_iterative(t1, 0, 0, t2);
  }else{
    assert read_char_io(t1, stdin, '(', true, ?t_open);
    assert read_char_io(_, stdin, ')', true, ?t_center);
    brackets_to_iterative(t_open);
    brackets_iterative_deepen(t1);
    
    brackets_to_iterative(t_center);
    brackets_iterative_concat(t1);
  }
}
@*/
