#ifndef ARRAYLIST_H
#define ARRAYLIST_H

struct arraylist;

/*@
predicate arraylist(struct arraylist *a; list<void*> vs);
@*/

struct arraylist *create_arraylist() ;
  //@ requires true;
  //@ ensures arraylist(result, nil);

void *list_get(struct arraylist *a, int i);
  //@ requires arraylist(a, ?vs) &*& 0 <= i &*& i < length(vs);
  //@ ensures arraylist(a, vs) &*& result == nth(i, vs);
  
int list_length(struct arraylist *a);
  //@ requires arraylist(a, ?vs);
  //@ ensures arraylist(a, vs) &*& result == length(vs);

void list_add(struct arraylist *a, void *v);
  //@ requires arraylist(a, ?vs);
  //@ ensures arraylist(a, append(vs, cons(v, nil)));
  
void list_remove_nth(struct arraylist *a, int n);
  //@ requires arraylist(a, ?vs) &*& 0 <= n &*& n < length(vs);
  //@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));

void list_dispose(struct arraylist* a);
  //@ requires arraylist(a, ?vs);
  //@ ensures true;

#endif