#ifndef SHARED_DEFINITIONS_H
#define SHARED_DEFINITIONS_H

#include <stddef.h>
#include <limits.h>
#include <stdbool.h>

//@ #include "nat.gh"

/*@

fixpoint bool collision_in_run();
fixpoint bool if_no_collision(bool formula)
{
  return collision_in_run() ? true : formula;
}

fixpoint int int_left(int p);
fixpoint int int_right(int p);
fixpoint int int_pair(int f, int s);

lemma_auto void int_left_int_pair(int f, int s);
  requires true;
  ensures  int_left(int_pair(f, s)) == f;

lemma_auto void int_right_int_pair(int f, int s);
  requires true;
  ensures  int_right(int_pair(f, s)) == s;

fixpoint int pow(int n, nat e) 
{
  switch (e)
  {
    case succ(e0): return n * pow(n, e0);
    case zero: return 1;
  }
} 

@*/

#endif
