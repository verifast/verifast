#include "malloc.h"

void set_to_zero(int* a, int N) 
  //@ requires array<int>(a, N, sizeof(int), integer, ?vs);
  //@ ensures array<int>(a, N, sizeof(int), integer, ?nvs) &*& forall_(i; i < 0 || i >= length(vs) || nth(i, nvs) == 0);
{
  int k = 0;
  while(k < N) 
    /*@ invariant 0 <= k &*& k <= N &*& 
                  array<int>(a, N, sizeof(int), integer, ?vs2) &*&
                  forall_(i; i < 0 || i >= k || nth(i, vs2) == 0);
    @*/
  {
    a[k] = 0;
    k++;
  }
}

void increment_all(int* a, int N) 
  //@ requires array<int>(a, N, sizeof(int), integer, ?vs);
  //@ ensures array<int>(a, N, sizeof(int), integer, ?nvs) &*& forall_(i; i < 0 || i >= length(vs) || nth(i, nvs) == nth(i, vs) + 1);
{
  int k = 0;
  while(k < N) 
    /*@ invariant 0 <= k &*& k <= N &*& 
                  array<int>(a, N, sizeof(int), integer, ?vs2) &*&
                  forall_(i; i < 0 || i >= k || nth(i, vs2) == nth(i, vs) + 1) &*&
                  forall_(i; i < k || i >= N || nth(i, vs2) == nth(i, vs));
    @*/
  {
    a[k] = a[k] + 1;
    k++;
  }
}