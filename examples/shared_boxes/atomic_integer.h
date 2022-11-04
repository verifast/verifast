#ifndef ATOMIC_INTEGER_H
#define ATOMIC_INTEGER_H

//@ predicate atomic_integer(int* i, real level, predicate(int) I);

/*@
lemma_auto void atomic_integer_inv();
    requires [?f]atomic_integer(?i, ?level, ?I);
    ensures [f]atomic_integer(i, level, I) &*& pointer_within_limits(i) == true;
@*/

/*@
lemma void create_atomic_integer(int* i, real upper_bound, predicate(int) I);
  requires integer(i, ?value) &*& I(value);
  ensures atomic_integer(i, ?new_level, I) &*& new_level < upper_bound;
@*/

/*@
predicate_family atomic_integer_set_pre(void* index)(int new_value);
predicate_family atomic_integer_set_post(void* index)(int old_value, int new_value);

typedef lemma void atomic_integer_set_lemma(int new_value, predicate(int) I, real level)();
  requires atomic_integer_set_pre(this)(new_value) &*& I(?value) &*& current_box_level(level);
  ensures atomic_integer_set_post(this)(value, new_value) &*& I(new_value) &*& current_box_level(level);
@*/

void atomic_integer_set(int* i, int v);  
  //@ requires [?f]atomic_integer(i, ?level, ?I) &*& is_atomic_integer_set_lemma(?lem, v, I, level)  &*& atomic_integer_set_pre(lem)(v);
  //@ ensures [f]atomic_integer(i, level, I) &*& atomic_integer_set_post(lem)(_, v);

/*@
predicate_family atomic_integer_get_pre(void* index)();
predicate_family atomic_integer_get_post(void* index)(int value);

typedef lemma void atomic_integer_get_lemma(predicate(int) I, real level)();
  requires atomic_integer_get_pre(this)() &*& I(?value) &*& current_box_level(level);
  ensures atomic_integer_get_post(this)(value) &*& I(value) &*& current_box_level(level);
@*/

int atomic_integer_get(int* i);
  //@ requires [?f]atomic_integer(i, ?level, ?I) &*& is_atomic_integer_get_lemma(?lem, I, level) &*& atomic_integer_get_pre(lem)();
  //@ ensures [f]atomic_integer(i, level, I) &*& atomic_integer_get_post(lem)(result);

/*@
predicate_family atomic_integer_cas_pre(void* index)(int old, int new);
predicate_family atomic_integer_cas_post(void* index)(bool success, int old, int new);

typedef lemma void atomic_integer_cas_lemma(predicate(int) I, int old, int new, real level)();
  requires atomic_integer_cas_pre(this)(old, new) &*& I(?value) &*& current_box_level(level);
  ensures atomic_integer_cas_post(this)(value == old, old, new) &*& I(value == old ? new : value) &*& current_box_level(level);
@*/

bool atomic_integer_cas(int* i, int old, int new);
  //@ requires [?f]atomic_integer(i, ?level, ?I) &*& is_atomic_integer_cas_lemma(?lem, I, old, new, level)  &*& atomic_integer_cas_pre(lem)(old, new);
  //@ ensures [f]atomic_integer(i, level, I) &*& atomic_integer_cas_post(lem)(result, old, new);
  
  /*@
predicate_family atomic_integer_inc_pre(void* index)();
predicate_family atomic_integer_inc_post(void* index)(int old);

typedef lemma void atomic_integer_inc_lemma(predicate(int) I, real level)();
  requires atomic_integer_inc_pre(this)() &*& I(?value) &*& current_box_level(level);
  ensures atomic_integer_inc_post(this)(value) &*& I(value + 1) &*& current_box_level(level);
@*/

int atomic_integer_inc(int* i);
  //@ requires [?f]atomic_integer(i, ?level, ?I) &*& is_atomic_integer_inc_lemma(?lem, I, level)  &*& atomic_integer_inc_pre(lem)();
  //@ ensures [f]atomic_integer(i, level, I) &*& atomic_integer_inc_post(lem)(result);

/*@
lemma void atomic_integer_dispose(int* i);
  requires atomic_integer(i, ?level, ?I);
  ensures integer(i, ?value) &*& I(value);
@*/

#endif
