#include "stdlib.h"
#include "assert.h"
#include "bool.h"
#include "malloc.h"
#include "list.h"
#include "listex.h"
#include "nat.h"

typedef int ElementType;

/*@
predicate heap(struct heap *heap, int size) =
  malloc_block_heap(heap)
  &*& heap->capacity |-> ?capacity
  &*& 0 <= capacity
  &*& 0 <= size
  &*& size + 1 <= capacity
  &*& heap->size |-> size
  &*& heap->elems |-> ?elems
  &*& array<int>(elems, size + 1, sizeof(int), integer, ?vs)
  &*& array<int>(elems + (size + 1), capacity - (size + 1), sizeof(int), integer, ?rest)
  &*& malloc_block(elems,4 * capacity)
  &*& forall_(i; i < 1 || i >= length(vs) || 2*i >= length(vs) || nth(i,vs) >= nth(2*i,vs))
  &*& forall_(i; i < 1 || i >= length(vs) || 2*i+1 >= length(vs) || nth(i,vs) >= nth(2*i+1,vs));
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
@*/

struct heap* heap_create(int capacity)
	//@ requires 0 <= capacity;
	//@ ensures heap(result, 0) &*& result != 0;
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
    	//@ close heap(q,0);
    	return q;
}

bool heap_is_empty(struct heap* heap)
	//@ requires heap(heap,?count);
	//@ ensures heap(heap,count) &*& result == (count == 0);
{
	//@ open heap(heap,count);
        return heap->size == 0;
        //@ close heap(heap,count);
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
@*/

void heap_insert(struct heap* heap, ElementType x)
  //@ requires heap(heap, ?count);
  //@ ensures heap(heap, count + 1);
{
  //@ open heap(heap, count);
  if(heap->size + 1 == heap->capacity) {
    abort();
  }
  //@ open array<int>(heap->elems + (heap->size + 1), heap->capacity - (heap->size + 1), sizeof(int), integer, ?rest);
  //@ move_array_elem(heap->elems, heap->size + 1);
  int in = ++heap->size;
  heap->elems[in] = x;
  swim(heap->elems, heap->size + 1, in);
  //@ close heap(heap, count + 1);
}

/*@
lemma void update_nth_lemma(list<int> vs, int k, int v)
  requires 0 <= k && k < length(vs);
  ensures forall_(i; i == k || nth(i, update(k, v, vs)) == nth(i, vs));
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(k != 0) {
        update_nth_lemma(t, k - 1, v);
      }
  }
}

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
  ////@ assert array<int>(arr, N, sizeof(int), integer, ?nvs);
  swim(arr, N, k /2);
}     

ElementType heap_max(struct heap* heap)
    	//@ requires heap(heap, ?count) &*& 0 < count;
	//@ ensures heap(heap, count);
{
	//@ open heap(heap, count);
	return heap->elems[1];
	//@ close heap(heap, count);
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



