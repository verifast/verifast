/*
This example shows that spinlock can be built on top of wrappers around atomic_integer.
*/

#include "atomic_integer.h"
#include "stdlib.h"

struct spinlock {
  int locked;
  //@ int locked_copy;
};

//@ predicate spinlock(struct spinlock* s, predicate() I) = atomic_integer(&s->locked, ?level, J(s, I)) &*& malloc_block_spinlock(s);

//@ predicate locked(struct spinlock* s, predicate() I, real f) = [f]atomic_integer(&s->locked, ?level, J(s, I)) &*& [f]malloc_block_spinlock(s) &*& [1/2]s->locked_copy |-> 1;

//@ predicate_ctor J(struct spinlock* s, predicate() I)(int state) = [1/2]s->locked_copy |-> state &*& state == 0 ? [1/2]s->locked_copy |-> 0 &*& I() : true;  

struct spinlock* create_spinlock() 
  //@ requires exists<predicate()>(?I) &*& I();
  //@ ensures spinlock(result, I);
{
  struct spinlock* s = malloc(sizeof(struct spinlock));
  if(s == 0) abort();
  s->locked = 0;
  s->locked_copy = 0;
  //@ close J(s, I)(0);
  //@ create_atomic_integer(&s->locked, 0, J(s, I));
  return s;
  //@ close spinlock(s, I);
}

void spinlock_acquire(struct spinlock* s)
  //@ requires [?f]spinlock(s, ?I);
  //@ ensures locked(s, I, f) &*& I();
{
  //@ open [f]spinlock(s, I);
  while(true) 
    //@ invariant [f]atomic_integer(&s->locked, ?level, J(s, I)) &*& [f]malloc_block_spinlock(s);
  {
    /*@
      predicate_family_instance atomic_integer_cas_pre(my_atomic_integer_cas_lemma)(int old, int new) = true;
      predicate_family_instance atomic_integer_cas_post(my_atomic_integer_cas_lemma)(bool success, int old, int new) = success ? I() &*& [1/2]s->locked_copy |-> 1 : true;
      lemma void my_atomic_integer_cas_lemma()
        requires atomic_integer_cas_pre(my_atomic_integer_cas_lemma)(0, 1) &*& J(s, I)(?value) &*& current_box_level(level);
        ensures atomic_integer_cas_post(my_atomic_integer_cas_lemma)(value == 0, 0, 1) &*& J(s, I)(value == 0 ? 1 : value) &*& current_box_level(level);
      {
        open atomic_integer_cas_pre(my_atomic_integer_cas_lemma)(0, 1);
        open J(s, I)(value);
        if(value == 0) { s->locked_copy = 1; }
        close J(s, I)(value == 0 ? 1 : value);
        close atomic_integer_cas_post(my_atomic_integer_cas_lemma)(0 == value, 0, 1);
      } 
    @*/
    //@  produce_lemma_function_pointer_chunk(my_atomic_integer_cas_lemma) : atomic_integer_cas_lemma(J(s, I), 0, 1, level)() { call(); };
    //@ close atomic_integer_cas_pre(my_atomic_integer_cas_lemma)(0, 1);
    bool success = atomic_integer_cas(&s->locked, 0, 1);
    //@ open atomic_integer_cas_post(my_atomic_integer_cas_lemma)(_, 0, 1);
    if(success) {
      break;
    }
  }
  //@ close locked(s, I, f);
}

void spinlock_release(struct spinlock* s)
  //@ requires locked(s, ?I, ?f) &*& I();
  //@ ensures [f]spinlock(s, I);
{
  //@ open locked(s, I, f);
  //@ assert [f]atomic_integer(_, ?level, _);
  {
    /*@
    predicate_family_instance atomic_integer_set_pre(my_atomic_integer_set_lemma)(int new) = I() &*& [1/2]s->locked_copy |-> 1;
    predicate_family_instance atomic_integer_set_post(my_atomic_integer_set_lemma)(int old, int new) = true;
    lemma void my_atomic_integer_set_lemma()
      requires atomic_integer_set_pre(my_atomic_integer_set_lemma)(0) &*& J(s, I)(?value) &*& current_box_level(level);
      ensures atomic_integer_set_post(my_atomic_integer_set_lemma)(value, 0) &*& J(s, I)(0) &*& current_box_level(level);
    {
      open atomic_integer_set_pre(my_atomic_integer_set_lemma)(0);
      open J(s, I)(value);
      s->locked_copy = 0;
      close J(s, I)(0);
      close atomic_integer_set_post(my_atomic_integer_set_lemma)(value, 0);
    } 
    @*/
    //@  produce_lemma_function_pointer_chunk(my_atomic_integer_set_lemma) : atomic_integer_set_lemma(0, J(s, I), level)() { call(); };
    //@ close atomic_integer_set_pre(my_atomic_integer_set_lemma)(0);
    atomic_integer_set(&s->locked, 0);
    //@ open atomic_integer_set_post(my_atomic_integer_set_lemma)(_, 0);
  }
  //@ close [f]spinlock(s, I);
}