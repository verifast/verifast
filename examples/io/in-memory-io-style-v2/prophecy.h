#ifndef __PROPHECY_H
#define __PROPHECY_H


//@ predicate prophecy_int(fixpoint(int, bool) invar, int val);

int prophecy_int_assign(int val);
//@ requires prophecy_int(?fp, _) &*& fp(val) == true;
//@ ensures [_]prophecy_int(fp, val) &*& result == val;

/**
 * Shows the prophecy invariant is true for the prophecy value
 * if the prophecy invariant is true for some prophecy value.
 * This condition is necessary, because we also support prophecies
 * for invariants that are always false, i.e. one that
 * cannot be instantiated.
 */
/*@
lemma void prophecy_invar(int val_prophecy, int val_instance);
requires
  [_]prophecy_int(?invar, val_prophecy)
  // Invar must be true for some value:
  &*& true == invar(val_instance);
ensures
  [_]prophecy_int(invar, val_prophecy)
  &*& true == invar(val_prophecy);
@*/

#endif
