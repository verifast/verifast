#include "malloc.h"
#include "stdlib.h"
#include "nat.h"
#include "arrays.h"
#include "listex.h"

struct heap {
  int* elems;
  int size;
  int capacity;
};

/*@
predicate heap(struct heap* h, int size, int capacity, list<int> vs) =
  h->elems |-> ?arr &*& h->capacity |-> capacity + 1 &*& array<int>(arr, capacity + 1, sizeof(int), integer, ?vs2) &*& is_heap(nat_of_int(length(take(size + 1, vs2))), take(size + 1, vs2), nil) == true &*& malloc_block(arr, 4 * (capacity + 1)) &*& h->size |-> size &*&
  0 <= size &*& size <= capacity &*& malloc_block_heap(h);

lemma void chars_to_intarray(void* arr, int capacity)
  requires chars(arr, ?vs) &*& length(vs) == 4*capacity &*& 0 <= capacity;
  ensures array<int>(arr, capacity, sizeof(int), integer, _);
{
  open chars(arr, vs);
  if(capacity == 0) {
  } else {
    switch(vs) { case nil: case cons(h, t): switch(t) { case nil: case cons(h0, t0): switch(t0) { case nil: case cons(h1, t1): }}};
    open chars(arr + 1, tail(vs));
    open chars(arr + 2, tail(tail(vs)));
    open chars(arr + 3, tail(tail(tail(vs))));
    chars_to_intarray(arr+4, capacity-1);
    close chars(arr+4, nil);
    close chars(arr + 3, cons(nth(3, vs), nil));
    close chars(arr + 2, cons(nth(2, vs), cons(nth(3, vs), nil)));
    close chars(arr + 1, cons(nth(1, vs), cons(nth(2, vs), cons(nth(3, vs), nil))));
    close chars(arr, cons(nth(0, vs), cons(nth(1, vs), cons(nth(2, vs), cons(nth(3, vs), nil)))));
    chars_to_integer(arr);
  }
}

fixpoint bool is_heap(nat i, list<int> vs, list<nat> except) {
  switch(i) {
    case zero: return true;
    case succ(i0): return (mem(i, except) || i  == zero || 
                          (
                            (2*int_of_nat(i) >= length(vs) || 0+ nth( int_of_nat(i), vs) <=  nth(int_of_nat(i)*2, vs)) &&
                            (2*int_of_nat(i) + 1 >= length(vs) || 0+ nth( int_of_nat(i), vs) <=  0 +nth(int_of_nat(i)*2 + 1, vs))
                          ))
                          && is_heap(i0, vs, except);
  }
}

lemma_auto(update(i, v, take(j, vs))) void update_take<t>(list<t> vs, int i, t v, int j)
  requires 0 <= i && 0 <= j && i <= j && j <= length(vs);
  ensures take(j, update(i, v, vs)) == update(i, v, take(j, vs));
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(i == 0) {
      } else {
        update_take(t, i - 1, v, j - 1);
      }
  }
}

lemma void mem_append<t>(t x, list<t> xs1, list<t> xs2) 
  requires true;
  ensures mem(x, append(xs1, xs2)) == (mem(x, xs1) || mem(x, xs2));
{
  switch(xs1) {
    case nil: 
    case cons(h, t):
      mem_append(x, t, xs2);
  }
}

lemma void is_heap_except_more(nat i, list<int> h, list<nat> except, list<nat> except2)
  requires is_heap(i, h, except) == true;
  ensures is_heap(i, h, append(except, except2)) == true;
{
  switch(i) {
    case zero:
    case succ(i0): 
      mem_append(i, except, except2);
      is_heap_except_more(i0, h, except, except2);
  }
}

lemma void is_heap_update(nat i, list<int> h, int j, int v)
  requires is_heap(i, h, nil) == true && 0 <= j && j < length(h) &*& ( 0 + (int) nth(j, h) <= v);
  ensures is_heap(i, update(j, v, h), cons(nat_of_int(j), nil)) == true;
{
  switch(i) {
    case zero:
    case succ(i0):
      is_heap_update(i0, h, j, v);
  }
}
@*/

struct heap* create_heap(int capacity)
  //@ requires 0 <= capacity;
  //@ ensures heap(result, 0, capacity, nil);
{
  struct heap* h = malloc(sizeof(struct heap));
  if(h == 0) abort();
  int* arr = malloc(sizeof(int)*(capacity + 1));
  if(arr == 0) abort();
  h->size = 0;
  h->capacity = capacity + 1;
  h->elems = arr;
  //@ chars_to_intarray(arr, capacity + 1);
  //@ succ_int(0);
  //@ close heap(h, 0, capacity, nil);
  return h;
}

void exch(int* arr, int i, int j)
  //@ requires array<int>(arr, ?capacity, sizeof(int), integer, ?vs) &*& 0 <= i &*& i < capacity &*& 0 <= j &*& j < capacity;
  //@ ensures array<int>(arr, capacity, sizeof(int), integer, update(j, nth(i, vs), update(i, nth(j, vs), vs)));
{
  int tmp = arr[i]; 
  arr[i] = arr[j];
  arr[j] = tmp;
}

/*@
lemma void is_heap_remove_except(nat i, list<int> h, nat exception)
  requires is_heap(i, h, cons(exception, nil)) == true &*& (0 + nth(int_of_nat(exception), h) <= 0+ nth( 2* int_of_nat(exception), h)) &*& (2*int_of_nat(exception)+1 >= length(h) || 0 + nth(int_of_nat(exception), h) <= 0+ nth( 2* int_of_nat(exception) +1, h));
  ensures is_heap(i, h, nil) == true;
{
  switch(i) {
    case zero:
    case succ(i0):
      is_heap_remove_except(i0, h, exception);
  }
}

lemma void is_heap_swap(nat i, list<int> h, int exc, int j);
  requires is_heap(i, h, cons(nat_of_int(exc), nil)) == true; // more assumptions needed here
  //((j == 2 * exc && nth(j, h) < nth(j + 1, h)) || (j == 2 * exc + 1 &&  nth(j -1, h) < nth(j, h))) &*& 0 + nth(j, h) < 0 + nth(exc, h);
  ensures is_heap(i, update(j, nth(exc, h), update(exc, nth(j, h), h)), cons(nat_of_int(j), nil)) == true;
/*{
  switch(i) {
    case zero:
    case succ(i0):
      is_heap_swap(i0, h, exc, j);
  }
}*/

lemma void is_heap_remove_excep(nat i, list<int> h, int exc)
  requires is_heap(i, h, cons(nat_of_int(exc), nil)) == true &*&  2 * exc >= length(h);
  ensures is_heap(i, h, nil) == true; 
{
  switch(i) {
    case zero:
    case succ(i0):
      is_heap_remove_excep(i0, h, exc);
  }
}

lemma void is_heap_shrink_list(nat i, list<int> h, list<nat> excep)
  requires is_heap(i, h, excep) == true &*& switch(h) { case nil: return false; case cons(first, last): return true; };
  ensures is_heap(i, take(length(h) -1, h), excep) == true;
{
  switch(i) {
    case zero:
    case succ(i0):
      is_heap_shrink_list(i0, h, excep);
  }
}

lemma int div2(int j); // todo: implement integer division
  requires 0 <= j;
  ensures 2 * result == j || 2 * result + 1 == j;
lemma void is_heap_smaller(nat i, list<int> h, int j)
  requires is_heap(i, h, nil) == true &*& 2*j < length(h) &*& 1 <= j&*& j <= int_of_nat(i);
  ensures 0 +nth(j, h) <= 0 +nth(2*j, h);
{
  switch(i) {
    case zero:
    case succ(i0):
      if(nat_of_int(j) == i) {
      } else {
        is_heap_smaller(i0, h, j);
      }
  }
}

lemma void is_heap_smaller2(nat i, list<int> h, int j)
  requires is_heap(i, h, nil) == true &*& 2*j + 1 < length(h) &*& 1 <= j &*& j <= int_of_nat(i);
  ensures 0 +nth(j, h) <= 0 +nth(2*j + 1, h);
{
  switch(i) {
    case zero: 
    case succ(i0):
      if(nat_of_int(j) == i) {
      } else {
        is_heap_smaller2(i0, h, j);
      }
  }
}

lemma void minimum_of_heap(nat i, list<int> h, int n)
  requires is_heap(i, h, nil) == true && 1 <= n &*& n < length(h) &*& n <= int_of_nat(i);
  ensures 0 + nth(1, h) <= nth(n, h);{
  int j = n;
  while(1 < j) 
    invariant 1 <= j &*& j <= n &*& 0+nth(j, h) <= 0 + nth(n, h);
    decreases j;
  {
    int oldj = j;
    j = div2(j);
    if(oldj == 2 * j) { 
      is_heap_smaller(i, h, j);
    } else {
      is_heap_smaller2(i, h, j);
    }
  }
}

@*/

void sink(int* arr, int size, int k)
  //@ requires array<int>(arr, ?capacity, sizeof(int), integer, ?vs2) &*& 1 <= k &*& k <= size+1 &*& size < capacity &*& is_heap(nat_of_int(length(take(size + 1, vs2))), take(size + 1, vs2), cons(nat_of_int(k), nil)) == true;
  //@ ensures array<int>(arr, capacity, sizeof(int), integer, ?vs2b) &*& is_heap(nat_of_int(length(take(size + 1, vs2b))), take(size + 1, vs2b), nil) == true;
{
  //@ int oldk = k;
  while(2*k <= size)
    //@ invariant oldk <= k &*& k <= size+1 &*& array<int>(arr, capacity, sizeof(int), integer, ?vs3) &*& is_heap(nat_of_int(length(take(size + 1, vs3))), take(size + 1, vs3), cons(nat_of_int(k), nil)) == true;
  {
    int j = 2 * k;
    if(j < size && arr[j] > arr[j + 1]) {
      j++;
    }
    if(! (arr[k] > arr[j])) {
      //@ is_heap_remove_except(nat_of_int(length(take(size + 1, vs3))), take(size + 1, vs3), nat_of_int(k));
      return;
    }
    exch(arr, k, j);
    //@ is_heap_swap(nat_of_int(length(take(size + 1, vs3))), take(size + 1, vs3), k, j);
    k = j;
  }
  //@ is_heap_remove_excep(nat_of_int(length(take(size + 1, vs3))), take(size + 1, vs3), k);
}

int extract_min(struct heap* h)
  //@ requires heap(h, ?size, ?cap, ?vs) &*& 0 < size;
  //@ ensures heap(h, size - 1, cap, _);
{
  //@ open heap(h, size, cap, vs);
  //@ int* arr = h->elems;
  //@ assert array<int>(arr, cap + 1, sizeof(int), integer, ?vs2);
  int res = h->elems[1];
  h->elems[1] = h->elems[h->size];
  //@  minimum_of_heap(nat_of_int(length(take(size + 1, vs2))), take(size + 1, vs2), size);
  //@ int last = nth(size, vs2);
  //@ is_heap_update(nat_of_int(length(take(size + 1, vs2))), take(size + 1, vs2), 1, nth(h->size, vs2));
  //@ update_take(vs2, 1, nth(h->size, vs2), size + 1);
  h->size--;
  //@ assert length(take(size + 1, vs2)) == length(take(size, vs2)) + 1;
  //@ succ_int(length(take(size, vs2)));
  //@ assert array<int>(arr, cap + 1, sizeof(int), integer, ?vs3);
  //@ is_heap_shrink_list(nat_of_int(length(take(size, vs3))), take(size + 1, vs3), cons(succ(zero), nil));
  //@ assume(take(length(take(size + 1, vs3)) - 1 , take(size + 1, vs3)) == take(size, vs3));
  sink(h->elems, h->size, 1);
  //@ close heap(h, size-1, cap, nil);
  return res;
}

/*void insert(struct heap* h, int x)
  //@ requires heap(h, ?size, ?cap, _) &*& size < cap;
  //@ ensures heap(h, size + 1, cap, _);
{
  //@ open heap(h, size, cap, _);
  h->elems[h->size + 1] = x;
  h->size++;
  swim(h->elems, h->size);
  //@ close heap(h, size+1, cap, _);
}

void swim(int* arr, int k) 
  //@ requires array<int>(arr, ?capacity, sizeof(int), integer, ?vs) &*& 1 <= k &*& k < capacity;
  //@ ensures array<int>(arr, capacity, sizeof(int), integer, _);
{
  //@ assume(false); // need to implement integer division
  //@ int oldk = k;
  while(1 < k && arr[k/2] < a[k])
    //@ invariant 1 <= k &*& k <= oldk &*& array<int>(arr, capacity, sizeof(int), integer, _);
  {
    exch(k / 2, k);
    k = k / 2;
  }
}*/

