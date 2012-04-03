#include "stdlib.h"
#include "assert.h"
#include "bool.h"
#include "malloc.h"
#include "list.h"

typedef int ElementType;

/*@
predicate heap(struct heap *heap, list<int> values) =
  malloc_block_heap(heap)
  &*& heap->capacity |-> ?capacity
  &*& 0 <= capacity
  &*& heap->size |-> ?size
  &*& length(values) == size
  &*& size + 1 <= capacity
  &*& heap->elems |-> ?elems
  &*& array<int>(elems, size + 1, sizeof(int), integer, ?vs)
  &*& tail(vs) == values
  &*& array<int>(elems + (size + 1), capacity - (size + 1), sizeof(int), integer, ?rest)
  &*& malloc_block(elems,4 * capacity)
  &*& forall_(i; i < 1 || i >= length(vs) || 2*i >= length(vs) || nth(i,vs) >= nth(2*i,vs))
  &*& forall_(i; i < 1 || i >= length(vs) || 2*i+1 >= length(vs) || nth(i,vs) >= nth(2*i+1,vs));
  //todo: &*& forall_(i; i < 1 || i >= length(vs) || nth(1, vs) >= nth(i, vs));
@*/		

struct heap
{
    int capacity;
    int size;
    ElementType *elems; 
};

/*@
lemma void multiply_positive(int i, int j) 
  requires i >= 0 &*& j >= 0;
  ensures i*j >= 0;
{
  assume(false);
}

lemma/*_auto(nth(i, update(j, y, xs)))*/ void nth_update2<t>(int i, int j, t y, list<t> xs)
    requires i != j;
    ensures nth(i, update(j, y, xs)) == nth(i, xs);
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(j == 0) {
        if(i == 0) {
        } else {
        }
      } else {
        if(i == 0) {
        } else {
          nth_update2<t>(i-1,j-1,y,t);
        }
      }
  }
}

lemma void nth_update3<t>(int i, t y, list<t> xs)
    requires 0 <= i && i < length(xs) ;
    ensures nth(i, update(i, y, xs)) ==  y;
{
  switch(xs) {
    case nil:
    case cons(h, t):

        if(i == 0) {
        } else {
        nth_update3<t>(i-1,y,t);
        }
  }
}
@*/

struct heap* heap_create(int capacity)
  //@ requires 0 <= capacity;
  //@ ensures heap(result, nil) &*& result != 0;
{
  struct heap* q;
  q = malloc(sizeof ( struct heap));
  if (q == 0) abort();
  if (sizeof(ElementType) == 0) abort();
  int acapacity = capacity + 1;
  int *array = malloc(4 * acapacity);
  if (array == 0) abort();
  //@ chars_to_intarray(array,acapacity);
  q->elems = array;
  if (q->elems == 0) abort();
  q->capacity = capacity + 1;
  q->size = 0;
  //@ open array<int>(array, capacity + 1, sizeof(int), integer, _);
  //@ close array<int>(array, 1, sizeof(int), integer, _);
  //@ close heap(q,nil);
  return q;
}

bool heap_is_empty(struct heap* heap)
	//@ requires heap(heap,?values);
	//@ ensures heap(heap,values) &*& result == (length(values) == 0);
{
	//@ open heap(heap,values);
        return heap->size == 0;
        //@ close heap(heap,values);
}

/*@
lemma void move_array_elem(int* arr, int N)
  requires array<int>(arr, N, sizeof(int), integer, ?vs1) &*& integer(arr + N, ?v);
  ensures array<int>(arr, N + 1, sizeof(int), integer, append(vs1, cons(v, nil)));
{
  switch(vs1) {
    case nil:
    case cons(h, t):
      open array<int>(arr, N, 4, integer, vs1);
      move_array_elem(arr + 1, N - 1);
  }
}
@*/

/*@
lemma_auto(nth(i, append(xs, ys))) void nth_append<t>(list<t> xs, list<t> ys, int i)
  requires 0 <= i && i < length(xs);
  ensures nth(i, xs) == nth(i, append(xs, ys));
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i == 0) {
      } else {
        nth_append(t, ys, i - 1);
      }
  }
}

lemma_auto(nth(i, append(xs, ys))) void nth_append2<t>(list<t> xs, list<t> ys, int i)
  requires length(xs) <= i && i < length(xs) + length(ys);
  ensures nth(i - length(xs), ys) == nth(i, append(xs, ys));
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i == 0) {
      } else {
        nth_append2(t, ys, i - 1);
      }
  }
}
lemma void update_nth_lemma(list<int> vs, int k, int v)
  requires 0 <= k && k < length(vs);
  ensures forall_(i; i == k || nth(i, update(k, v, vs)) == nth(i, vs)) &*& nth(k, update(k, v, vs)) == v;
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(k != 0) {
        update_nth_lemma(t, k - 1, v);
      }
  }
}
@*/

void heap_insert(struct heap* heap, ElementType x)
  //@ requires heap(heap, ?values);
  //@ ensures heap(heap, ?values2) &*& length(values2) == length(values) + 1;
{
  //@ open heap(heap, values);
  //@ int* arr = heap->elems;
  if(heap->size + 1 == heap->capacity) {
    abort();
  }
  //@ open array<int>(heap->elems + (heap->size + 1), heap->capacity - (heap->size + 1), sizeof(int), integer, ?rest);
  //@ move_array_elem(heap->elems, heap->size + 1);
  int in = ++heap->size;
  //@ assert array<int>(arr, length(values) + 2, sizeof(int), integer, ?es);
  heap->elems[in] = x;
  //@ assert 0 <= in && in < length(es);
  //@ update_nth_lemma(es, in , x);
  swim(heap->elems, heap->size + 1, in);
  //@ assert array<int>(arr, in + 1, sizeof(int), integer, ?values2);
  //@ switch(values2) { case nil: case cons(h, t): }
  //@ close heap(heap, tail(values2));
}

/*@
lemma_auto(i/2) void div_mul(int i);
  requires true;
  ensures 2*(i/2) == i || 2*(i/2) + 1 == i || i < 1;

lemma_auto(i/2) void div_bounds(int i);
  requires true;
  ensures i < 1 || (0 < i / 2 && i/2 < i);
  
@*/
void swim(int* arr, int N, int k)
  /*@ requires array<int>(arr, N, sizeof(int), integer, ?vs) &*& 0 < k &*& k < N &*& 
               forall_(i; i < 1 || 2*i == k || i >= length(vs) || 2*i >= length(vs) || nth(i,vs) >= nth(2*i,vs)) &*&
               forall_(i; i < 1 || 2*i + 1 == k || i >= length(vs) || 2*i+1 >= length(vs) || nth(i,vs) >= nth(2*i+1,vs)) &*&
               (k == 1 || 2*k >= length(vs) || nth(k/2, vs) >= nth(2*k, vs)) &*&
               (k == 1 || 2*k + 1 >= length(vs) || nth(k/2, vs) >= nth(2*k + 1, vs)); @*/
  /*@ ensures array<int>(arr, N, sizeof(int), integer, ?vs2) &*& 
              forall_(i; i < 1 || i >= length(vs2) || 2*i >= length(vs2) || nth(i,vs2) >= nth(2*i,vs2)) &*&
              forall_(i; i < 1 || i >= length(vs2) || 2*i+1 >= length(vs2) || nth(i,vs2) >= nth(2*i+1,vs2)); @*/
{
  if(k == 1) {
    return;
  }
  if(arr[k/2] >= arr[k]) {
    return;
  }
  int tmp = arr[k];
  arr[k] = arr[k/2];
  arr[k/2] = tmp;
  //@ update_nth_lemma(vs, k, nth(k / 2, vs));
  //@ update_nth_lemma(update(k, nth(k/2, vs), vs), k/2, nth(k, vs));
  swim(arr, N, k /2);
}

ElementType heap_max(struct heap* heap)
  //@ requires heap(heap, ?values) &*& 0 < length(values);
  //@ ensures heap(heap, values);//todo &*& forall_(i; i < 0 || i >= length(values) || result >= nth(i, values));
{
  //@ open heap(heap, values);
  return heap->elems[1];
  //@ close heap(heap, values);
}


int main()
  //@ requires true;
  //@ ensures true;
{
    ElementType max;
    struct heap* q = heap_create(6);
    bool empty = heap_is_empty(q);
    assert(empty);
    heap_insert(q,2);
    empty = heap_is_empty(q);
    assert(!empty);
    heap_insert(q,5);
    heap_insert(q,3);
    heap_insert(q,6);
    heap_insert(q,9);
    heap_insert(q,10);
    return 0;
    //@ leak heap(q,_); //TO BE REMOVED
}



