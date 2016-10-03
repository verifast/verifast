#ifndef PROPHECY_H
#define PROPHECY_H

//@ predicate prophecy(int prophetic_value);

// Note: don't simply use a lemma instead of a C function. With a lemma
// there would be an unsoundness, exploitable like this:
//  //@ assert prophecy(id, ?val); prophecy_assign(id, val+1); assert val == val+1;
void prophecy_assign(int real_value);
//@ requires prophecy(?prophetic_value);
//@ ensures real_value == prophetic_value;

/*@
lemma int create_prophecy();
requires true;
ensures prophecy(result);
@*/

#endif
