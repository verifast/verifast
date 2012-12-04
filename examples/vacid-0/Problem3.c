#include "malloc.h"
#include "stdlib.h"
//@ #include "nat.gh"
//@ #include "arrays.gh"
//@ #include "listex.gh"

struct heap {
  int* elems;
  int size;
  int capacity;
};

/*@
predicate heap(struct heap* h, int size, int capacity, list<int> vs) =
  h->elems |-> ?arr &*& h->capacity |-> capacity + 1 &*& arr[0..capacity + 1] |-> ?vs2 &*&
  is_heap(nat_of_int(length(take(size + 1, vs2))), take(size + 1, vs2), nil) == true &*&
  malloc_block_ints(arr, capacity + 1) &*& h->size |-> size &*&
  0 <= size &*& size <= capacity &*& malloc_block_heap(h);

fixpoint bool is_perm<t>(list<t> xs, list<t> ys)
{
  switch(xs) {
    case nil: return ys == nil;
    case cons(h, t):
      return mem(h, ys) && is_perm(t, remove(h, ys));
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

lemma_auto(take(j, update(i, v, vs))) void update_take2<t>(list<t> vs, int i, t v, int j)
  requires 0 <= i && 0 <= j && i <= j && j <= length(vs);
  ensures take(j, update(i, v, vs)) == update(i, v, take(j, vs));
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(i == 0) {
      } else {
        update_take2(t, i - 1, v, j - 1);
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
  //@ succ_int(0);
  //@ assert arr[0..capacity + 1] |-> ?vs2;
  //@ switch(vs2) { case nil: case cons(h0, t0): }
  //@ assert take(1, vs2) == cons(nth(0, vs2), nil);
  //@ close heap(h, 0, capacity, nil);
  return h;
}

void exch(int* arr, int i, int j)
  //@ requires arr[0..?capacity] |-> ?vs &*& 0 <= i &*& i < capacity &*& 0 <= j &*& j < capacity;
  //@ ensures arr[0..capacity] |-> update(j, nth(i, vs), update(i, nth(j, vs), vs));
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

lemma_auto void is_perm_reflexive<t>(list<t> xs) 
  requires true;
  ensures is_perm(xs, xs) == true;
{
  switch(xs) {
    case nil: 
    case cons(h, t): 
      switch(t) {
        case nil:
        case cons(h0, t0):
          is_perm_reflexive(t);
      }
  }
}

lemma void is_perm_swap<t>(list<t> vs, int i, int j);
  requires 0 <= i &*& 0 <= j &*& i < length(vs) &*& j < length(vs);
  ensures is_perm(update<t>(i, nth<t>(j, vs), update<t>(j, nth<t>(i, vs), vs)), vs) == true;



fixpoint int count_eq<t>(t x, list<t> xs) {
  switch(xs) {
    case nil: return 0;
    case cons(h, t): return h == x ? 1 + count_eq(x, t) : count_eq(x, t);
  }
}

fixpoint bool count_same<t>(unit u, list<t> vs, list<t> vs2, t x) {
  switch(u) {
    case unit: return count_eq(x, vs) == count_eq(x, vs2);
  }
}

lemma_auto(count_eq(x, vs)) void count_eq_non_negative<t>(t x, list<t> vs)
  requires true;
  ensures 0 <= count_eq(x, vs);
{
  switch(vs) {
    case nil:
    case cons(h, t):
      count_eq_non_negative(x, t);
  }
}

lemma_auto(count_eq(x, remove(x, vs))) void count_eq_remove<t>(t x, list<t> vs)
  requires true;
  ensures count_eq(x, remove(x, vs)) == (mem(x, vs) ? count_eq(x, vs) - 1 : count_eq(x, vs));
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(h != x) {
        count_eq_remove<t>(x, t);
      }
  }
}

lemma_auto(mem(x, vs)) void mem_count_eq<t>(t x, list<t> vs)
  requires  true;
  ensures mem(x, vs) == (0 < count_eq(x, vs));
{
  switch(vs) {
    case nil:
    case cons(h, t):
      mem_count_eq(x, t);
  }
}


lemma void is_perm_same_counts<t>(list<t> vs, list<t> vs2);
  requires length(vs) == length(vs2) &*& forall(vs, (count_same)(unit, vs, vs2)) == true;
  ensures is_perm(vs, vs2) == true;
/*{
  switch(vs) {
    case nil:
      switch(vs2) { case nil: case cons(h0, t0): }
    case cons(h, t):
      assert count_same(unit, vs, vs2, h) == true;
      assert mem(h, vs2) == true;
      assert count_same(unit, t, remove(h, vs2), h) == true;
      is_perm_same_counts(t, remove(h, vs2));
  }
}*/

lemma void is_heap_swap(nat i, list<int> h, int k, int prevk)
  requires is_heap(i, h, cons(nat_of_int(k), nil)) == true &*& int_of_nat(i) <= length(h) &*& 1 <= k &*& 2*k < length(h) &*& (2*k >= length(h)-1 || nth<int>(2*k, h) <= nth<int>(2*k + 1, h)) &*& nth<int>(2*k, h) <= nth(k, h) &*& k == 1 || 2 * prevk == k || 2 * prevk  + 1 == k &*&  k == 1 ? true : nth<int>(prevk, h) <= nth(2*k, h);
  ensures is_heap(i, update(2*k, nth(k, h), update(k, nth(2*k, h), h)), cons(nat_of_int(2*k), nil)) == true;
{
  switch(i) {
    case zero:
    case succ(i0): 
      is_heap_swap(i0, h, k, prevk);
  }
}

lemma void is_heap_swap2(nat i, list<int> h, int k, int prevk)
  requires is_heap(i, h, cons(nat_of_int(k), nil)) == true &*& int_of_nat(i) <= length(h) &*& 1 <= k &*& 2*k +1< length(h) &*& (nth<int>(2*k+1, h) <= nth<int>(2*k, h)) &*& nth<int>(2*k+1, h) <= nth(k, h) &*& k == 1 || 2 * prevk == k || 2 * prevk  + 1 == k &*&  k == 1 || 2 * k + 1 >= length(h) ? true : nth<int>(prevk, h) <= nth(2*k+1, h); 
  ensures is_heap(i, update(2*k + 1, nth(k, h), update(k, nth(2*k + 1, h), h)), cons(nat_of_int(2*k + 1), nil)) == true;
{
  switch(i) {
    case zero:
    case succ(i0): 
      is_heap_swap2(i0, h, k, prevk);
  }
}

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

lemma void is_heap_e_smaller(nat i, list<int> h, int e, int j)
  requires is_heap(i, h, cons(nat_of_int(e), nil)) == true &*& 1 <= e &*& e <= length(h) &*& 2*j < length(h) &*& 1 <= j&*& j <= int_of_nat(i) &*& e != j ;
  ensures 0 +nth(j, h) <= 0 +nth(2*j, h);
{
  switch(i) {
    case zero:
    case succ(i0):
      if(nat_of_int(j) == i) {
      } else {
        is_heap_e_smaller(i0, h, e, j);
      }
  }
}

lemma void is_heap_e_smaller2(nat i, list<int> h, int e, int j)
  requires is_heap(i, h, cons(nat_of_int(e), nil)) == true &*& 1 <= e &*& e <= length(h) &*& 2*j + 1 < length(h) &*& 1 <= j&*& j <= int_of_nat(i) &*& e != j ;
  ensures 0 +nth(j, h) <= 0 +nth(2*j + 1, h);
{
  switch(i) {
    case zero:
    case succ(i0):
      if(nat_of_int(j) == i) {
      } else {
        is_heap_e_smaller2(i0, h, e, j);
      }
  }
}

lemma void is_heap_smaller2(nat i, list<int> h, int j)
  requires is_heap(i, h, nil) == true &*& 2*j + 1 < length(h) &*& 1 <= j &*& j <= int_of_nat(i) ;
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
  ensures 0 + nth(1, h) <= nth(n, h);
{
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


lemma void is_perm_transitive(list<int> xs, list<int> ys, list<int> zs);
  requires is_perm(xs, ys) == true &*& is_perm(ys, zs)== true;
  ensures is_perm(xs, zs) == true;
  
lemma void is_perm_symmetric<t>(list<t>xs, list<t> ys);
  requires is_perm(xs, ys) == true;
  ensures is_perm(ys, xs) == true;

lemma void take_take<t>(list<t> xs, int i, int j)
  requires 0 <= i  && i <= j && j <= length(xs);
  ensures take(i, take(j, xs)) == take(i, xs);
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i == 0) {
      } else {
        take_take(t, i - 1, j - 1);
      }
  }
}

fixpoint bool le(unit u, int x, int y) {
  switch(u) { 
    case unit: return x <= y;
  }
}

@*/

void sink(int* arr, int size, int k)
  //@ requires arr[0..?capacity] |-> ?vs2 &*& k == 1 &*& 1 <= k &*& k <= size+1 &*& size < capacity &*& is_heap(nat_of_int(length(take(size + 1, vs2))), take(size + 1, vs2), cons(nat_of_int(k), nil)) == true;
  //@ ensures arr[0..capacity] |-> ?vs2b &*& is_heap(nat_of_int(length(take(size + 1, vs2b))), take(size + 1, vs2b), nil) == true &*& is_perm(take(size + 1, vs2), take(size+ 1, vs2b)) == true;
{
  //@ int prevk = div2(k); 
  //@ int oldk = k;
  while(2*k <= size)
    //@ invariant k == 1 || 2* prevk ==k || 2*prevk+1 == k &*& oldk <= k &*& k <= size+1 &*& arr[0..capacity] |-> ?vs3 &*& (1 < k && 2*k < size + 1 ? nth<int>(prevk, vs3) <= nth(2*k, vs3) : true) &*& (1 < k && 2*k +1< size + 1 ? nth<int>(prevk, vs3) <= nth(2*k+1, vs3) : true) &*& is_heap(nat_of_int(length(take(size + 1, vs3))), take(size + 1, vs3), cons(nat_of_int(k), nil)) == true &*& is_perm(take(size + 1, vs2), take(size + 1, vs3)) == true;
  {
    int j = 2 * k;
    if(j < size && arr[j] > arr[j + 1]) {
      j++;
    } 
    if (2*j < size + 1) {
      //@ is_heap_e_smaller(nat_of_int(size + 1), take(size + 1, vs3), k, j); 
    }
    if(2*j + 1 < size + 1) {
      //@ is_heap_e_smaller(nat_of_int(size + 1), take(size + 1, vs3), k, j); 
      //@ is_heap_e_smaller2(nat_of_int(size + 1), take(size + 1, vs3), k, j);
    }
    if(! (arr[k] > arr[j])) {
      //@ is_heap_remove_except(nat_of_int(length(take(size + 1, vs3))), take(size + 1, vs3), nat_of_int(k));
      return;
    }
    exch(arr, k, j);
    //@ is_perm_swap(take(size + 1, vs3), j, k);
    //@ assert arr[0..capacity] |-> ?myvs;
    //@ assert is_perm(take(size + 1, myvs), take(size + 1, vs3)) == true;
  
    //@ is_perm_symmetric(take(size + 1, myvs), take(size + 1, vs3));
    //@ is_perm_transitive(take(size + 1, vs2), take(size + 1, vs3), take(size + 1, myvs));
    if(j == 2 * k) {
       //@ is_heap_swap(nat_of_int(length(take(size + 1, vs3))), take(size + 1, vs3), k, prevk);
    } else {
       //@ is_heap_swap2(nat_of_int(length(take(size + 1, vs3))), take(size + 1, vs3), k, prevk);
    }
    k = j;
    //@ prevk = div2(k);
  }
  //@ is_heap_remove_excep(nat_of_int(length(take(size + 1, vs3))), take(size + 1, vs3), k);
}

/*@
fixpoint int minimum(list<int> xs) {
  switch(xs) {
    case nil: return 0;
    case cons(h, t): return h < minimum(t) ? h : minimum(t);
      
  }
}



fixpoint int min(int x, list<int> xs) {
    switch (xs) {
        case nil: return x;
        case cons(x0, xs0): return x > x0 ? min(x0, xs0) : min(x, xs0);
    }
}


@*/

int extract_min(struct heap* h)
  //@ requires heap(h, ?size, ?cap, ?vs) &*& 0 < size;
  //@ ensures heap(h, size - 1, cap, remove(result, vs));
  
{
  //@ open heap(h, size, cap, vs);
  //@ int* arr = h->elems;
  //@ assert arr[0..cap + 1] |-> ?vs2;
  int res = h->elems[1];
  h->elems[1] = h->elems[h->size];
  //@ minimum_of_heap(nat_of_int(length(take(size + 1, vs2))), take(size + 1, vs2), size);
  //@ is_heap_update(nat_of_int(length(take(size + 1, vs2))), take(size + 1, vs2), 1, nth(h->size, vs2));
  //@ update_take(vs2, 1, nth(h->size, vs2), size + 1);
  h->size--;
  //@ succ_int(length(take(size, vs2)));
  //@ assert arr[0..cap + 1] |-> ?vs3;
  //@ is_heap_shrink_list(nat_of_int(length(take(size, vs3))), take(size + 1, vs3), cons(succ(zero), nil));
  //@ take_take(vs3, size, size + 1);
  sink(h->elems, h->size, 1);
  //@ assert arr[0..cap + 1] |-> ?vsa;
  //@ assert is_perm(take(size, vs3), take(size, vsa)) == true;
  //@ close heap(h, size-1, cap, remove(res, vs)); // todo
  return res;
}


/*@
lemma_auto(take(j, update(i, v, vs))) void take_update<t>(list<t> vs, int i, t v, int j)
  requires 0 <= i && 0 <= j && j <= length(vs) && j <= i;
  ensures take(j, vs) == take(j, update(i, v, vs));
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(j == 0) {
      } else {
        take_update(t, i - 1, v, j - 1);
      }
  }
}

lemma_auto(nth(i, append(vs1, vs2))) void nth_append<t>(list<t> vs1, list<t> vs2, int i)
  requires 0 <= i && i < length(vs1) + length(vs2);
  ensures nth(i, append(vs1, vs2)) == (i < length(vs1) ? nth(i, vs1) : nth(i - length(vs1), vs2));
{
  switch(vs1) {
    case nil:
    case cons(h, t):
      if(i == 0) {
      } else {
        nth_append(t, vs2, i - 1);
      }
  }
} 

lemma void is_heap_extend(nat i, list<int> vs, int x, int prev)
  requires is_heap(i, vs, nil) == true &*& 2*prev == length(vs) || 2*prev +1 == length(vs) || length(vs) == 1;
  ensures is_heap(i, append(vs, cons(x, nil)), cons(nat_of_int(prev), nil)) == true;
{
  switch(i) {
    case zero:
      succ_int(0);
    case succ(i0):
      is_heap_extend(i0, vs, x, prev);
  }
}

lemma_auto(append(take(j, vs), cons(nth(j, vs), nil))) void take_plus_one_auto<t>(list<t> vs, int j)
  requires 0 <= j && j < length(vs);
  ensures take(j + 1, vs) == append(take(j, vs), cons(nth(j, vs), nil));
{
  take_plus_one(j, vs);
}

lemma void mylemma(nat i, list<int> h, int k, int prevk)
  requires is_heap(i, h, cons(nat_of_int(prevk), nil)) == true &*& 0 <= prevk &*& 1 <= k &*& k <length(h) &*& 2 * prevk == k || 2 * prevk + 1 == k &*& k != 1 &*& nth<int>(prevk, h) <= nth(2 * prevk, h) &*&  2*prevk+1 >= length(h) || nth<int>(prevk, h) <= nth(2 *prevk + 1, h);// &*& 2*k >= length(h) || nth<int>(prevk, h) <= nth(2*k, h) &*&  2*k + 1 >= length(h) || nth<int>(prevk, h) <= nth(2*k + 1, h);
  ensures is_heap(i, h, nil) == true;
{
  switch(i) {
    case zero:
    case succ(i0):
      mylemma(i0, h, k, prevk);
      if(int_of_nat(i) == prevk) {
        
      } else {
      }
  }
}

lemma void is_heap_zero_excep(nat i, list<int> h)
  requires is_heap(i, h, cons(zero, nil)) == true;
  ensures is_heap(i, h, nil) == true;
{
  switch(i) {
    case zero:
    case succ(i0):
      is_heap_zero_excep(i0, h);
  }
}

lemma void is_heap_swap3(nat i, list<int> h, int k, int prevk, int newprevk)
  requires is_heap(i, h, cons(nat_of_int(prevk), nil)) == true &*& 1 <= k && k < length(h) &*& 2*prevk == k || 2*prevk + 1 == k &*& (2*prevk == k && 2*prevk + 1 < length(h) ? nth<int>(prevk, h) <= nth(2*prevk + 1, h) : true) &*& (2*prevk + 1 == k ? nth<int>(prevk, h) <= nth<int>(2*prevk, h) : true ) &*& 2*newprevk == prevk || 2*newprevk+1 == prevk &*& nth<int>(k, h) < nth<int>(prevk, h) &*& 2*k >= length(h) || nth<int>(prevk, h) <= nth(2*k, h) &*& 2*k + 1 >= length(h) || nth<int>(prevk, h) <= nth(2*k + 1, h);
  ensures is_heap(i, update(k, nth(prevk, h), update(prevk, nth(k, h), h)), cons(nat_of_int(newprevk), nil)) == true;
{
  switch(i) {
    case zero:
    case succ(i0): 
      is_heap_swap3(i0, h, k, prevk, newprevk);
      if(int_of_nat(i) == newprevk) {
      } else {
        if(int_of_nat(i) == prevk) {
        } else {
          if(int_of_nat(i) == k) {
          assume(false);
          } else {
             
          }
        }
      }
  }
}
@*/

int div2real(int j); // todo: implement integer division
  //@ requires 0 <= j;
  //@ ensures 2 * result == j || 2 * result + 1 == j;

void swim(int* arr, int size, int k) 
  //@ requires arr[0..?capacity] |-> ?vs &*& 1 <= k &*& k < size+1 &*& size + 1 <= capacity &*& ghostparam(?prevkk) &*& is_heap(nat_of_int(size + 1), take(size + 1, vs), cons(nat_of_int(prevkk), nil)) == true  &*& 2 * prevkk == k || 2 * prevkk + 1 == k &*& (k == 1 ? true : (2*prevkk == k ? 2*prevkk +1 >= size + 1 || nth<int>(prevkk, vs) <= nth<int>(2*prevkk + 1, vs) : nth<int>(prevkk, vs) <= nth<int>(2*prevkk, vs)))  &*& 2*k >= size + 1 || nth<int>(prevkk, vs) <= nth(2*k, vs) &*& 2*k + 1 >= size + 1 || nth<int>(prevkk, vs) <= nth(2*k + 1, vs); 
  //@ ensures arr[0..capacity] |-> ?vs2 &*& is_heap(nat_of_int(size + 1), take(size + 1, vs2), nil) == true;
{
  //@ assume(false);
  //@ open ghostparam(prevkk);
  //@ int oldk = k;
  int prevk = div2real(k);
  //@ assert prevk == prevkk;
  while(1 < k && arr[prevk] > arr[k])
    //@ invariant 1 <= k &*& 0 <= prevk &*& prevk <= k &*& k <= oldk &*& array<int>(arr, capacity, sizeof(int), integer, ?vss) &*& 2 * prevk == k || 2 * prevk + 1 == k &*& (k == 1 ? true : (2*prevk == k ? 2*prevk +1 >= size + 1 || nth<int>(prevk, vss) <= nth<int>(2*prevk + 1, vss) : nth<int>(prevk, vss) <= nth<int>(2*prevk, vss))) &*& is_heap(nat_of_int(size + 1), take(size + 1, vss), cons(nat_of_int(prevk), nil)) == true &*& k == 1 || 2*k >= size + 1 || nth<int>(prevk, vss) <= nth(2*k, vss) &*& k == 1 || 2*k + 1 >= size + 1 || nth<int>(prevk, vss) <= nth(2*k + 1, vss);
  {
    exch(arr, prevk, k);
    int prek = k;
    //@ assert array<int>(arr, capacity, sizeof(int), integer, ?vsss);
    int newprevk = div2real(prevk);
    //@ is_heap_swap3(nat_of_int(size + 1), take(size + 1, vss), k, prevk, newprevk);
    k = prevk;
    prevk = newprevk;
    /*@
    if(2* prevk ==  k) {
      is_heap_e_smaller(nat_of_int(size + 1), take(size + 1, vss), k, prevk);
      if(2*prevk +1 < size + 1) {
        
        is_heap_e_smaller2(nat_of_int(size + 1), take(size + 1, vss), k, prevk);
      } else {
      }
    } else {
      if(1 <= prevk) {
        is_heap_e_smaller(nat_of_int(size + 1), take(size + 1, vss), k, prevk);
      }
    }
    @*/
    /*@
    if(k  == 1) {
    } else {
      if(2* prevk == k && prek == 2*k) {
      } else if(2* prevk == k && prek == 2*k+1) {
      } 
      else {
       if(2*k == prek) {
         assert nth<int>(prek, vss) < nth<int>(k, vss); 
         if(2*k+1 < size + 1) {
           assert nth<int>(k, vss) <= nth<int>(2*k+1, vss);
         }
         is_heap_e_smaller2(nat_of_int(size + 1), take(size + 1, vss), k, prevk);
       } else {
         assert nth<int>(prek, vss) < nth<int>(k, vss); 
         if(2*k < size + 1) {
           assert nth<int>(k, vss) <= nth<int>(2*k, vss);
         }
         is_heap_e_smaller2(nat_of_int(size + 1), take(size + 1, vss), k, prevk);
         is_heap_e_smaller(nat_of_int(size + 1), take(size + 1, vss), k, prevk);
       }
      }
    }
    @*/
  }
  /*@
  if(k == 1) {
    is_heap_zero_excep(nat_of_int(size + 1), take(size + 1, vss));
  } else {
    mylemma(nat_of_int(size + 1), take(size + 1, vss), k, prevk);
  }
  @*/
}

//@ predicate ghostparam<t>(t x) = true;

void insert(struct heap* h, int x)
  //@ requires heap(h, ?size, ?cap, ?vs) &*& size < cap;
  //@ ensures heap(h, size + 1, cap, cons(x, vs));
{
  //@ open heap(h, size, cap, _);
  //@ assert ints(?arr, cap + 1, ?vsa);
  //@ assert is_heap(nat_of_int(size + 1), take(size + 1, vsa), nil) == true; 
  h->elems[h->size + 1] = x;
  //@ assert ints(arr, cap + 1, ?vsa2);
  //@ assert take(size + 1, vsa2) == take(size +1, vsa);
  //@ assert is_heap(nat_of_int(size + 1), take(size + 1, vsa2), nil) == true; 
  h->size++;
  //@ assert nth(size +1, vsa2) == x;
  //@ int prevk = div2(size+1);
  //@ is_heap_extend(nat_of_int(size + 1), take(size + 1, vsa2), x, prevk);
  //@ assert is_heap(nat_of_int(size + 1), append(take(size + 1, vsa2), cons(x, nil)), cons(nat_of_int(prevk), nil)) == true;
  //@ take_plus_one(size + 1, vsa2);
  //@ assert is_heap(nat_of_int(size + 1), take(size + 2, vsa2), cons(nat_of_int(prevk), nil)) == true;
  //@ succ_int(size + 1);
  //@ assert is_heap(nat_of_int(size + 2), take(size + 2, vsa2), cons(nat_of_int(prevk), nil)) == true;
  //@ close ghostparam(prevk);
  //@ assert 2*prevk == size + 1 || 2*prevk +1 == size + 1;
  //@ int tmp = h->size;
  //@ assert tmp == size + 1;
  /*@
  if(2*prevk == size +1) {
    
  } else {
    if(2 * prevk + 1 == size + 1) {
      if(1 <= prevk) {
        is_heap_smaller(nat_of_int(size + 1), take(size + 1, vsa), prevk);
      }
    }
  }
  @*/
  swim(h->elems, h->size, h->size);
  //@ close heap(h, size+1, cap, cons(x, vs)); //todo
}


