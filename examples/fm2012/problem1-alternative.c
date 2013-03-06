// uses SMT solver quantifiers to encode forall_

int lcp(int *a, int N, int x, int y)
  //@ requires [?f]a[0..N] |-> ?elems &*& 0 <= x &*& x < N &*& 0 <= y &*& y < N;
  /*@ ensures [f]a[0..N] |-> elems &*& 
              forall_(int i; i < x || i < y || x + result <= i || x + result <= i || nth(i, elems) == nth(i, elems)) &*&
              (x + result == N || y + result == N || nth(x + result, elems) != nth(y + result, elems)); @*/
{
  int l = 0;
  while(x + l < N && y + l < N && a[x + l] == a[y + l])
    /*@ invariant [f]a[0..N] |-> elems &*& 0 <= l &*& x + l <= N &*& y + l <= N &*&
                  forall_(int i; i < x || i < y || x + l <= i || x + l <= i || nth(i, elems) == nth(i, elems)); @*/
    //@ decreases N - l;
  {
    l++;
  }
  return l;
}