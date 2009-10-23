#ifndef PRELUDE_CORE_H
#define PRELUDE_CORE_H

/*@

fixpoint t default<t>();

inductive unit = unit;

inductive boxed_int = boxed_int(int);
fixpoint int unboxed_int(boxed_int i) { switch (i) { case boxed_int(value): return value; } }

inductive boxed_bool = boxed_bool(bool);
fixpoint bool unboxed_bool(boxed_bool b) { switch (b) { case boxed_bool(value): return value; } }

inductive boxed_real = boxed_real(real);
fixpoint real unboxed_real(boxed_real r) { switch (r) { case boxed_real(value): return value; } }

@*/

#endif