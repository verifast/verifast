// uses SMT solver quantifiers to encode forall_

// Using the nth_eq auxiliary function in the forall_ bodies is necessary to ensure that
// the SMT solver can identify a trigger pattern for quantifier instantiation. The
// straightforward form
//
//     forall_(int i; i < 0 || nth(x + i, elems) == nth(y + i, elems) || result <= i)
//
// does not work because the terms nth(x + i, elems) and nth(y + i, elems) are not
// appropriate trigger terms, because i appears in these terms only under an arithmetic
// operator, which is dealt with specially and is not suitable for syntactic matching.

//@ fixpoint bool nth_eq<t>(int x, int y, int i, list<t> xs) { return nth(x + i, xs) == nth(y + i, xs); }

int lcp(int *a, int N, int x, int y)
  //@ requires [?f]a[0..N] |-> ?elems &*& 0 <= x &*& x <= N &*& 0 <= y &*& y <= N;
  /*@ ensures [f]a[0..N] |-> elems &*& 0 <= result &*& x + result <= N &*& y + result <= N &*&
              forall_(int i; i < 0 || nth_eq(x, y, i, elems) || result <= i) &*&
              x + result == N || y + result == N || nth(x + result, elems) != nth(y + result, elems); @*/
{
  int l = 0;
  while(x + l < N && y + l < N && a[x + l] == a[y + l])
    /*@ invariant [f]a[0..N] |-> elems &*& 0 <= l &*& x + l <= N &*& y + l <= N &*&
                  forall_(int i; i < 0 || nth_eq(x, y, i, elems) || l <= i); @*/
    //@ decreases N - l;
  {
    l++;
  }
  return l;
}