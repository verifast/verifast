#ifndef LISTS_H
#define LISTS_H

#include "list.h"

struct list;
struct iter;

/*@

predicate list(struct list* l, list<void *> v);
predicate iter(struct iter* i, struct list* l, list<void *> v, int index);

@*/

struct list *create_list();
  //@ requires emp;
  //@ ensures list(result, nil);
struct iter *list_create_iter(struct list *list);
  //@ requires list(list, ?xs);
  //@ ensures iter(result, list, xs, 0);
bool iter_has_next(struct iter *iter);
  //@ requires iter(iter, ?l, ?xs, ?i);
  //@ ensures iter(iter, l, xs, i) &*& result == (i < length(xs));
void *iter_next(struct iter *iter);
  //@ requires iter(iter, ?l, ?xs, ?i) &*& i < length(xs);
  //@ ensures iter(iter, l, xs, i + 1) &*& result == nth(i, xs);
void iter_dispose(struct iter *iter);
  //@ requires iter(iter, ?l, ?xs, ?i);
  //@ ensures list(l, xs);
void list_add(struct list *list, void *element);
  //@ requires list(list, ?xs);
  //@ ensures list(list, cons(element, xs));
void list_remove(struct list *list, void *element);
  //@ requires list(list, ?xs) &*& mem(element, xs) == true;
  //@ ensures list(list, remove(element, xs));
void list_dispose(struct list *list);
  //@ requires list(list, _);
  //@ ensures emp;

#endif