#ifndef __PROPHECY_H
#define __PROPHECY_H


//@ predicate prophecy_int(fixpoint(int, bool) invar, int val;);

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
  prophecy_int(?invar, val_prophecy)
  // Invar must be true for some value:
  &*& true == invar(val_instance);
ensures
  prophecy_int(invar, val_prophecy)
  &*& true == invar(val_prophecy);
@*/

/**
 * Creates a prophecy.
 *
 * Note that we do not require that the invariant is true for some value,
 * if it is not, you simply cannot use it.
 */
/*@
lemma int prophecy_create(fixpoint(int, bool) invar);
requires true;
ensures prophecy_int(invar, result);
@*/

#endif
