#include "malloc.h"

void set_to_zero(int* a, int N) 
  //@ requires a[0..N] |-> ?vs;
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == 0);
{
  int k = 0;
  while(k < N) 
    /*@ invariant 0 <= k &*& k <= N &*& 
                  a[0..N] |-> ?vs2 &*&
                  forall_(int i; i < 0 || i >= k || nth(i, vs2) == 0);
    @*/
  {
    a[k] = 0;
    k++;
  }
}

void increment_all(int* a, int N) 
  //@ requires a[0..N] |-> ?vs;
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == nth(i, vs) + 1);
{
  int k = 0;
  while(k < N) 
    /*@ invariant 0 <= k &*& k <= N &*& 
                  a[0..N] |-> ?vs2 &*&
                  forall_(int i; i < 0 || i >= k || nth(i, vs2) == nth(i, vs) + 1) &*&
                  forall_(int i; i < k || i >= N || nth(i, vs2) == nth(i, vs));
    @*/
  {
    a[k] = a[k] + 1;
    k++;
  }
}
