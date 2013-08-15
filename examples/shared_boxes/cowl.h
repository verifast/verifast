#ifndef COWL_H
#define COWL_H

struct list;

//@ predicate list(struct list* l, list<int> values);

struct list* create_cow_list();
  //@ requires true;
  //@ ensures result == 0 ? true : list(result, nil);
  
struct list* copy_cow_list(struct list* src);
  //@ requires list(src, ?values);
  //@ ensures list(src, values) &*& result == 0 ? true : list(result, values);

void cow_list_insert(struct list* l, int x);
  //@ requires list(l, ?values);
  //@ ensures list(l, cons(x, values));

void cow_list_set(struct list* l, int i, int x);
  //@ requires list(l, ?values) &*& 0 <= i &*& i < length(values);
  //@ ensures list(l, update(i, x, values));

void cow_list_dispose(struct list* l);
  //@ requires list(l, ?values);
  //@ ensures true;

#endif
