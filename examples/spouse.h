#ifndef SPOUSE_H
#define SPOUSE_H

struct person;

/*@
predicate person(struct person *p, struct person *spouse);
@*/

struct person *create_person();
  //@ requires true;
  //@ ensures person(result, 0) &*& result != 0;

void marry(struct person *this, struct person *other);
  //@ requires person(this, 0) &*& person(other, 0);
  //@ ensures person(this, other) &*& person(other, this);
  
struct person* person_get_spouse(struct person* this);
  //@ requires person(this, ?spouse);
  //@ ensures person(this, spouse) &*& result == spouse;

void divorce(struct person *this);
  //@ requires person(this, ?other) &*& person(other, this);
  //@ ensures person(this, 0) &*& person(other, 0);
  
/*@
lemma void married_lemma(struct person *this);
  requires person(this, ?other) &*& person(other, ?t);
  ensures person(this, other) &*& person(other, t) &*& t == this;
  
lemma void person_diff(struct person *this, struct person* other);
  requires person(this, ?t) &*& person(other, ?o);
  ensures person(this, t) &*& person(other, o) &*& this != other;
  
lemma void spouse_diff(struct person *this);
  requires person(this, ?t);
  ensures person(this, t) &*& this != t;
@*/

void die(struct person *this);
  //@ requires person(this, ?other) &*& (other == 0 ? true : person(other, this));
  //@ ensures other == 0 ? true : person(other, 0);

#endif