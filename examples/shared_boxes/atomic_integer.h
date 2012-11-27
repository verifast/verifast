#ifndef ATOMIC_INTEGER_H
#define ATOMIC_INTEGER_H

//@ predicate atomic_integer(int* i, predicate(int) I);

/*@
lemma void create_atomic_integer(int* i, predicate(int) I);
  requires integer(i, ?value) &*& I(value);
  ensures atomic_integer(i, I);
@*/

/*@
predicate_family atomic_integer_set_pre(void* index)(int new_value);
predicate_family atomic_integer_set_post(void* index)(int old_value, int new_value);

typedef lemma void atomic_integer_set_lemma(int new_value, predicate(int) I)();
  requires atomic_integer_set_pre(this)(new_value) &*& I(?value);
  ensures atomic_integer_set_post(this)(value, new_value) &*& I(new_value);
@*/

void atomic_integer_set(int* i, int v);  
  //@ requires [?f]atomic_integer(i, ?I) &*& is_atomic_integer_set_lemma(?lem, v, I)  &*& atomic_integer_set_pre(lem)(v);
  //@ ensures [f]atomic_integer(i, I) &*& atomic_integer_set_post(lem)(_, v);

/*@
predicate_family atomic_integer_get_pre(void* index)();
predicate_family atomic_integer_get_post(void* index)(int value);

typedef lemma void atomic_integer_get_lemma(predicate(int) I)();
  requires atomic_integer_get_pre(this)() &*& I(?value);
  ensures atomic_integer_get_post(this)(value) &*& I(value);
@*/

int atomic_integer_get(int* i);
  //@ requires [?f]atomic_integer(i, ?I) &*& is_atomic_integer_get_lemma(?lem, I)  &*& atomic_integer_get_pre(lem)();
  //@ ensures [f]atomic_integer(i, I) &*& atomic_integer_get_post(lem)(result);

/*@
predicate_family atomic_integer_cas_pre(void* index)(int old, int new);
predicate_family atomic_integer_cas_post(void* index)(bool success, int old, int new);

typedef lemma void atomic_integer_cas_lemma(predicate(int) I, int old, int new)();
  requires atomic_integer_cas_pre(this)(old, new) &*& I(?value);
  ensures atomic_integer_cas_post(this)(value == old, old, new) &*& I(value == old ? new : value);
@*/

bool atomic_integer_cas(int* i, int old, int new);
  //@ requires [?f]atomic_integer(i, ?I) &*& is_atomic_integer_cas_lemma(?lem, I, old, new)  &*& atomic_integer_cas_pre(lem)(old, new);
  //@ ensures [f]atomic_integer(i, I) &*& atomic_integer_cas_post(lem)(result, old, new);

/*@
lemma void atomic_integer_dispose(int* i);
  requires atomic_integer(i, ?I);
  ensures integer(i, ?value) &*& I(value);
@*/


#endif
