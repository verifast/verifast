//@ #include "quantifiers.gh"
//@ #include "range.gh"

/*@
fixpoint bool ok(list<int> elems, int x, int y, int i) {
  return nth(x + i, elems) == nth(y + i, elems);
}
@*/

int lcp(int *a, int N, int x, int y)
  //@ requires [?f]a[0..N] |-> ?elems &*& 0 <= x &*& x < N &*& 0 <= y &*& y < N;
  /*@ ensures [f]a[0..N] |-> elems &*& 
              0 <= result && result <= N - x && result <= N - y && 
              forall(range(0, result), (ok)(elems, x, y)) == true &*&
              x + result == N || y + result == N || nth(x + result, elems) != nth(y + result, elems); @*/
{
  int l = 0;
  while(x + l < N && y + l < N && a[x + l] == a[y + l])
    /*@ invariant [f]a[0..N] |-> elems &*& 0 <= l &*& x + l <= N &*& y + l <= N &*&
                  forall(range(0, l), (ok)(elems, x, y)) == true; @*/
    //@ decreases N - l;
  {
    l++;
    /*@
    if(! forall(range(0,l), (ok)(elems, x, y))) {
       int i = not_forall(range(0, l), (ok)(elems, x, y));
       if(i < l - 1) {
         forall_elim(range(0, l - 1), (ok)(elems, x, y), i);
       }
    }
    @*/
  }
  return l;
}