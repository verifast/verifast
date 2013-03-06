// uses native quantifiers
// only verifies with Z3

int lcp(int *a, int N, int x, int y)
    //@ requires [?f]a[0..N] |-> ?elems &*& 0 <= x &*& x < N &*& 0 <= y &*& y < N;
    /*@ ensures [f]a[0..N] |-> elems &*& 
                forall_(int i; i < 0 || i >= result || nth(x + i, elems) == nth(y + i, elems)) &*&
                (x + result == N || y + result == N || nth(x + result, elems) != nth(y + result, elems));
                 @*/
{
  int l = 0;
  while(x + l < N && y + l < N && a[x + l] == a[y + l])
    /*@ invariant [f]a[0..N] |-> elems &*& 0 <= l &*& x + l <= N &*& y + l <= N &*&
                  forall_(int i; nth(x + i, elems) == nth(y + i, elems) || i < 0 || i >= l); @*/
    //@ decreases N - l;
  {
    l++;
  }
  return l;
  
}