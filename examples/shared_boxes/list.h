#ifndef __LIST_H
#define __LIST_H

//@ predicate list(struct list* l; list<void*> vs);

struct list;

struct list* create_list();
  //@ requires true;
  //@ ensures list(result, nil); 
  
void list_add_first(struct list* l, void* p);
  //@ requires list(l, ?vs);
  //@ ensures list(l, cons(p, vs));
  
struct list* list_remove_all(struct list* l);
  //@ requires list(l, ?vs);
  //@ ensures list(l, nil) &*& result != 0 &*& list(result, vs);

void* list_remove_first(struct list* l);
  //@ requires list(l, ?vs) &*& vs != nil;
  //@ ensures list(l, tail(vs)) &*& result == head(vs); 
  
bool list_contains(struct list* l, void* p);
  //@ requires list(l, ?vs);
  //@ ensures list(l, vs) &*& result == mem(p, vs);

bool list_is_empty(struct list* l);
  //@ requires list(l, ?vs);
  //@ ensures list(l, vs) &*& result == (vs == nil);

void list_dispose(struct list* l);
  //@ requires list(l, _);
  //@ ensures true;
  
#endif
