#include "stdlib.h"
#include "malloc.h"
#include "string.h"
#include "arraylist.h"

struct arraylist {
  void *data;
  int size;
  int capacity;
};

/*@
predicate pointer_array(void* data, list<void*> vs) =
  switch(vs) { 
    case nil: return true;
    case cons(h, t): return pointer(data, h) &*& pointer_array(data + sizeof(void*), t);
  };
  
lemma void pointer_array_to_chars(void* data);
  requires pointer_array(data, ?vs);
  ensures chars(data, ?vs2) &*& length(vs2) == length(vs) * sizeof(void*) &*& vs2 == pointers_as_char_list(vs);

lemma void chars_to_pointer_array(void* data);
  requires chars(data, ?vs);
  ensures pointer_array(data, ?vs2) &*& length(vs2) * sizeof(void*) == length(vs) &*& vs2 == char_list_as_pointers(vs);

fixpoint list<char> pointers_as_char_list(list<void*> c);
fixpoint list<void*> char_list_as_pointers(list<char> c);

lemma void char_list_to_pointers(list<void*> c);
  requires true;
  ensures char_list_as_pointers(pointers_as_char_list(c)) == c;
  
lemma void split_pointer_array(void* data, int i);
  requires pointer_array(data, ?vs) &*& 0<=i &*& i <= length(vs);
  ensures pointer_array(data, take(i, vs)) &*& pointer_array(data + (i *(sizeof(void*))), drop(i, vs));

lemma void merge_pointer_array(void* data, int i);
  requires pointer_array(data, ?vs) &*& pointer_array(data + (i * sizeof(void*)), ?vs2);
  ensures pointer_array(data, append(vs, vs2));

predicate arraylist(struct arraylist *a, list<void*> vs) =
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*&
  malloc_block_arraylist(a) &*& malloc_block(data, capacity * sizeof(void*)) &*& 0<=size &*& size <= capacity &*& size == length(vs) &*&
  pointer_array(data, vs) &*& chars((void*) data + (size * sizeof(void*)), ?unused) &*& length(unused) == 4 * (capacity - size);
@*/

struct arraylist *create_arraylist() 
  //@ requires true;
  //@ ensures arraylist(result, nil);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  //@ close pointer_array(data, nil);
  //@ close arraylist(a, nil);
  return a; 
}

/*@
lemma void nth_drop<t>(list<t> xs, int i);
  requires 0<= i &*& i < length(xs);
  ensures nth(i, xs) == head(drop(i, xs));
  
lemma void append_drop_take<t>(list<t> xs, int i);
  requires 0 <= i &*& i <= length(xs);
  ensures append(take(i, xs), drop(i, xs)) == xs;
@*/

void *list_get(struct arraylist *a, int i)
  //@ requires arraylist(a, ?vs) &*& 0 <= i &*& i < length(vs);
  //@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
  //@ open arraylist(a, vs);
  void** data = a->data;
  //@ split_pointer_array(data, i);
  //@ open pointer_array(data + i, drop(i, vs));
  //@ length_drop(i, vs);
  void* res = *(data + i);
  //@ close pointer_array(data + i, drop(i, vs));
  //@ merge_pointer_array(data, i);
  return res;
  //@ append_drop_take(vs, i);
  //@ nth_drop(vs, i);
  //@ close arraylist(a, vs);
}

int list_length(struct arraylist *a)
  //@ requires arraylist(a, ?vs);
  //@ ensures arraylist(a, vs) &*& result == length(vs);
{
  //@ open arraylist(a, vs);
  return a->size;
  //@ close arraylist(a, vs);
}

/*@
lemma void append_length<t>(list<t> xs1, list<t> xs2);
  requires true;
  ensures length(append(xs1, xs2)) == length(xs1) + length(xs2);
@*/

void list_add(struct arraylist *a, void *v)
  //@ requires arraylist(a, ?vs);
  //@ ensures arraylist(a, append(vs, cons(v, nil)));
{
  int size = 0;
  void** data = 0;
  //@ open arraylist(a, vs);
  if(a->capacity == a->size) {
    data = a->data;
    size = a->size;
    int capacity = a->capacity;
    void** newData = malloc((capacity + 100) * sizeof(void*));
    if(newData == 0) abort();
    //@ assert chars((void*) newData, ?junk);
    //@ chars_split((void*) newData, size * sizeof(void*));
    //@ pointer_array_to_chars(data);
    memcpy(newData, data, size * sizeof(void*));
    //@  chars_to_pointer_array(newData);
    a->data = newData;
    a->capacity = capacity + 100;
    //@ chars_join((void*) data);
    free(data);
    //@ char_list_to_pointers(vs);
  }
  size = a->size;
  data = a->data;
  //@ assert chars((void*) data + (size * sizeof(void*)), ?unused); 
  //@ chars_split((void*) (data + size), 4);
  //@ chars_to_pointer(data + size);
  * (data + size) = v;
  //@ assert data + size + 1 == data + size + 1;
  //@ close pointer_array((data + size) + 1, nil);
  //@ close pointer_array(data + size, cons(v, nil));
  //@ merge_pointer_array(data, size);
  a->size += 1;
  //@ append_length(vs, cons(v, nil));
  //@ close arraylist(a, append(vs, cons(v, nil)));
}

void shift(void** data, int n) 
  //@ requires pointer_array(data, ?vs) &*& 0 <= n &*& n + 1 == length(vs);
  //@ ensures pointer_array(data, tail(vs)) &*& chars((void*) data + (n*sizeof(void*)), ?cs) &*& length(cs) == sizeof(void*);
{
  if(n == 0) {
    //@ switch(vs) { case nil: case cons(h, t): switch(t) { case nil: case cons(h0, t0): } }
    //@ assert tail(vs) == nil;
    //@ pointer_array_to_chars(data);
    //@ close pointer_array(data, nil);
  } else {
    //@ open pointer_array(data, vs);
    //@ assert pointer_array(data + 1, ?t);
    //@ open pointer_array(data + 1, t);
    * (data) = *(data + 1);
    //@ close pointer_array(data + 1, t);
    shift(data + 1, n - 1);
    //@ close pointer_array(data, tail(vs));
  }
}

void list_remove_nth(struct arraylist *a, int n)
  //@ requires arraylist(a, ?vs) &*& 0 <= n &*& n < length(vs);
  //@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
{
  //@ open arraylist(a, vs);
  void** data = a->data;
  int size = a->size;
  int i = n;
  //@ split_pointer_array(data, n);
  //@ length_drop(n, vs);
  //@ length_take(n, vs);
  //@ assert size == length(vs);
  shift(data + (n), size - n - 1);
  //@ merge_pointer_array(data, n);
  //@ chars_join((void*)data + (size - 1)*4);
  //@ switch(drop(n, vs)) { case nil: case cons(h0, t0): }
  a->size = a->size - 1;
  //@ assert length(tail(drop(n, vs))) == length(vs) - n - 1;
  //@ length_append(take(n, vs), tail(drop(n, vs)));
  //@ close arraylist(a, append(take(n, vs), tail(drop(n, vs))));
}

void list_dispose(struct arraylist* a)
  //@ requires arraylist(a, ?vs);
  //@ ensures true;
{
  //@ open arraylist(a, vs);
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  //@ pointer_array_to_chars(data);
  //@ chars_join((void*) data);
  free(data);
  free(a);
}

void main() 
  //@ requires true;
  //@ ensures true;
{
  struct arraylist* a = create_arraylist();
  void* tmp = 0;
  list_add(a, 0);
  list_add(a, 0);
  
  tmp = list_get(a, 1);
  //@ assert tmp == 0;
  list_dispose(a);
}


