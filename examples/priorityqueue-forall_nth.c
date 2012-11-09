#include "stdlib.h"
#include "assert.h"
#include "bool.h"
#include "malloc.h"

//@ #include "quantifiers.gh"
//@ #include "arrays.gh"

typedef int ElementType;

/*@

fixpoint bool heap_index(list<int> xs, int i) {
  return 
    i < 1 || 
    i >= length(xs) || 
    (
      (2*i >= length(xs) || nth(i,xs) >= nth(2*i,xs)) && 
      (2*i + 1 >= length(xs) || nth(i,xs) >= nth(2*i + 1,xs))
    );
}

fixpoint bool heap_index_e(int except, list<int> xs, int i) {
  return 
    i < 1 || 
    i >= length(xs) || 
    (
      (2*i >= length(xs) || 2*i == except || nth(i,xs) >= nth(2*i,xs)) && 
      (2*i + 1 >= length(xs) || 2*i + 1 == except || nth(i,xs) >= nth(2*i + 1,xs))
    );
}

fixpoint bool ge(int v, list<int> vs, int index) { return v >= nth(index, vs); }

fixpoint bool ge_nth(int i, list<int> vs, int index) { return nth(i, vs) >= nth(index, vs) || index == 0; }

fixpoint bool ge_nth_except(int i, int except, list<int> vs, int index) { return index == except || nth(i, vs) >= nth(index, vs) || index == 0; }

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
  &*& forall_nth(vs, heap_index) == true
  &*& switch(values) { case nil: return true; case cons(h, t): return forall_nth(vs, (ge_nth)(1)) == true; };
@*/		

struct heap
{
    int capacity;
    int size;
    ElementType *elems; 
};

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
  //@ chars_to_int_array(array,acapacity);
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
lemma void merge_array(int* arr)
  requires array<int>(arr, ?N, sizeof(int), integer, ?vs1) &*& array<int>(arr + N, ?M, sizeof(int), integer, ?vs2);
  ensures array<int>(arr, N + M, sizeof(int), integer, append(vs1, vs2));
{
  switch(vs1) {
    case nil:
    case cons(h, t):
      open array<int>(arr, N, sizeof(int), integer, vs1);
      merge_array(arr + 1);
  }
}


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

lemma void intarray_to_chars(void* a)
  requires array<int>(a, ?n, sizeof(int), integer, _);
  ensures chars(a, ?cs) &*& length(cs) == n * sizeof(int);
{
  if(n == 0) {
    close chars(a, nil);
  } else {
    open array<int>(a, n, sizeof(int), integer, _);
    integer_to_chars(a);
    intarray_to_chars(a + sizeof(int));
    chars_join(a);
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
  //@ assert array<int>(arr, length(values) + 1, sizeof(int), integer, ?vs);
  //@ open array<int>(heap->elems + (heap->size + 1), heap->capacity - (heap->size + 1), sizeof(int), integer, ?rest);
  //@ move_array_elem(heap->elems, heap->size + 1);
  /*@
  if(! forall_nth(append(vs, cons(head(rest), nil)), (heap_index_e)(length(vs)))) {
    int i = not_forall_nth(append(vs, cons(head(rest), nil)), (heap_index_e)(length(vs)));
    nth_append(vs, cons(head(rest), nil), i);
    forall_nth_elim(vs, heap_index, i);
    nth_append(vs, cons(head(rest), nil), 2*i);
    nth_append(vs, cons(head(rest), nil), 2*i + 1);
  } 
  @*/
  int in = ++heap->size;
  //@ assert array<int>(arr, length(values) + 2, sizeof(int), integer, ?es);
  heap->elems[in] = x;
  //@ assert array<int>(arr, length(values) + 2, sizeof(int), integer, ?us);
  //@ assert 0 <= in && in < length(es);
  /*@
  if(! forall_nth(update(length(es) - 1, x, es), (heap_index_e)(length(es) - 1))) {
    int i = not_forall_nth(update(length(es) - 1, x, es), (heap_index_e)(length(es) - 1));
    forall_nth_elim(es, (heap_index_e)(length(es) - 1), i);
  }
  @*/
  /*@
  if(in != 1) {
    if(! forall_nth(append(vs, cons(head(rest), nil)), (ge_nth_except)(1, length(vs)))) {
      int i = not_forall_nth(append(vs, cons(head(rest), nil)),(ge_nth_except)(1, length(vs)));
      nth_append(vs, cons(head(rest), nil), i);
      nth_append(vs, cons(head(rest), nil), 1);
      forall_nth_elim(vs, (ge_nth)(1), i);
    }
  }
  @*/
  /*@
    if(in != 1) {
      if(! forall_nth(update(length(es) - 1, x, es), (ge_nth_except)(1, length(es)-1))) {
        int i = not_forall_nth(update(length(es) - 1, x, es), (ge_nth_except)(1, length(es)-1));
        forall_nth_elim(es, (ge_nth_except)(1, length(es)-1), i);
      }
    } else {
      if(!forall_nth(us, (ge_nth_except)(1, 1))) {
        int i = not_forall_nth(us, (ge_nth_except)(1, 1));
      }
    }
  @*/
  swim(heap->elems, heap->size + 1, in);
  //@ assert array<int>(arr, in + 1, sizeof(int), integer, ?values2);
  //@ switch(values2) { case nil: case cons(h, t): switch(t) { case nil: case cons(h0, t0): } }
  //@ close heap(heap, tail(values2));
}

/*@
lemma_auto(i/2) void div_mul(int i)
  requires 1 < i;
  ensures 2*(i/2) == i || 2*(i/2) + 1 == i;
{
  assume(false);
}
@*/

void swim(int* arr, int N, int k)
  /*@ requires array<int>(arr, N, sizeof(int), integer, ?vs) &*& 0 < k &*& k < N &*& 
               forall_nth(vs, (heap_index_e)(k)) == true &*&
               (k == 1 || 2*k >= length(vs) || nth(k/2, vs) >= nth(2*k, vs)) &*&
               (k == 1 || 2*k + 1 >= length(vs) || nth(k/2, vs) >= nth(2*k + 1, vs)) &*&
               forall_nth(vs, (ge_nth_except)(1, k)) == true; @*/
  /*@ ensures array<int>(arr, N, sizeof(int), integer, ?vs2) &*& 
              forall_nth(vs2, heap_index) == true &*&
              forall_nth(vs2, (ge_nth)(1)) == true; @*/
{
  if(k == 1) {
    /*@
    if(! forall_nth(vs, heap_index)) {
      int i = not_forall_nth(vs, heap_index);
      forall_nth_elim(vs, (heap_index_e)(k), i);
    }
    @*/
    /*@
    if(!  forall_nth(vs, (ge_nth)(1))) {
      int i = not_forall_nth(vs, (ge_nth)(1));
      forall_nth_elim(vs, (ge_nth_except)(1, k), i);
    }
    @*/
    return;
  }
  if(arr[k/2] >= arr[k]) {
    /*@
    if(! forall_nth(vs, heap_index)) {
      int i = not_forall_nth(vs, heap_index);
      forall_nth_elim(vs, (heap_index_e)(k), i);
    }
    @*/
    /*@
    if(!  forall_nth(vs, (ge_nth)(1))) {
      int i = not_forall_nth(vs, (ge_nth)(1));
      forall_nth_elim(vs, (ge_nth_except)(1, k), i);
      forall_nth_elim(vs, (ge_nth_except)(1, k), k/2);
    }
    @*/
    return;
  }
  int tmp = arr[k];
  arr[k] = arr[k/2];
  arr[k/2] = tmp;
  //@ list<int> nvs = update(k/2, nth(k, vs), update(k, nth(k/2, vs), vs));
  //@ int nk = k / 2;
  /*@
  if(! forall_nth(nvs, (heap_index_e)(k/2))) {
    int i = not_forall_nth(nvs, (heap_index_e)(k/2));
    forall_nth_elim(vs, (heap_index_e)(k), i);
  }
  @*/
  /*@
    if(!  forall_nth(nvs, (ge_nth_except)(1, k/2))) {
      int i = not_forall_nth(nvs, (ge_nth_except)(1, k/2));
      forall_nth_elim(vs, (ge_nth_except)(1, k), i);
      forall_nth_elim(vs, (ge_nth_except)(1, k), k/2);
    }
    @*/
  /*@
  if(nk > 1) {
    forall_nth_elim(vs, (heap_index_e)(k), nk/2);
  } @*/
  //@ forall_nth_elim(vs, (heap_index_e)(k), k/2);
  swim(arr, N, k/2);
}

ElementType heap_max(struct heap* heap)
  //@ requires heap(heap, ?values) &*& 0 < length(values);
  //@ ensures heap(heap, values) &*& forall_nth(values, (ge)(result)) == true &*& mem(result, values) == true;
{
  //@ open heap(heap, values);
  //@ int tmp = heap->elems[1];
  //@ int* elems = heap->elems;
  //@ assert array<int>(elems, _, _, _, ?vs);
  return heap->elems[1];
  /*@
  if(! forall_nth(values, (ge)(tmp))) {
    int i = not_forall_nth(values, (ge)(tmp));
    forall_nth_elim(vs, (ge_nth)(1), i + 1);
  }
  @*/
  //@ switch(vs) { case nil: case cons(h, t): }
  //@ close heap(heap, values);
}

int heap_size(struct heap* heap)
  //@ requires heap(heap, ?values);
  //@ ensures heap(heap, values) &*& result == length(values);
{
  //@ open heap(heap, values);
  return heap->size;
  //@ close heap(heap, values);
}

void heap_dispose(struct heap* heap)
  //@ requires heap(heap, ?values) ;
  //@ ensures true;
{
  //@ open heap(heap, values);
  //@ merge_array(heap->elems);
  //@ intarray_to_chars(heap->elems);
  free((void*) (heap->elems));
  free(heap);
}

int main() //@: main
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
    max = heap_max(q);
    // assert max == 10; // todo
    heap_dispose(q);
    return 0;
}



