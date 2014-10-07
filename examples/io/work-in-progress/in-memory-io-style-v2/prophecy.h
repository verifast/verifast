#ifndef __PROPHECY_H
#define __PROPHECY_H


//@ predicate prophecy<t>(fixpoint(t, bool) invar, t val;);

void prophecy_int_assign(int val);
//@ requires prophecy<int>(?fp, ?prophetic_value) &*& fp(val) == true;
//@ ensures [_]prophecy<int>(fp, prophetic_value) &*& val == prophetic_value;

/**
 * Shows the prophecy invariant is true for the prophecy value
 * if the prophecy invariant is true for some prophecy value.
 * This condition is necessary, because we also support prophecies
 * for invariants that are always false, i.e. one that
 * cannot be instantiated.
 */
/*@
lemma void prophecy_invar<t>(t val_prophecy, t val_instance);
requires
  prophecy<t>(?invar, val_prophecy)
  // Invar must be true for some value:
  &*& true == invar(val_instance);
ensures
  prophecy<t>(invar, val_prophecy)
  &*& true == invar(val_prophecy);
@*/

/**
 * Creates a prophecy.
 *
 * Note that we do not require that the invariant is true for some value,
 * if it is not, you simply cannot use it.
 */
/*@
lemma t prophecy_create<t>(fixpoint(t, bool) invar);
requires true;
ensures prophecy<t>(invar, result);
@*/

#endif
