/*@
fixpoint boolean forall_nth_core<t>(list<t> xs, fixpoint(list<t>, int, boolean) p, nat n) {
  switch(n) {
    case zero: return p(xs, int_of_nat(zero));
    case succ(n0): return p(xs, int_of_nat(n)) && forall_nth_core(xs, p, n0);
  }
}

fixpoint boolean forall_nth<t>(list<t> xs, fixpoint(list<t>, int, boolean) p) {
  switch(xs) {
    case nil: return true;
    case cons(h, t): return forall_nth_core(xs, p, nat_of_int(length(xs) - 1));
  }
}

lemma int not_forall_nth_nat<t>(list<t> vs, fixpoint (list<t>, int, boolean) p, nat n)
  requires ! forall_nth_core(vs, p, n);
  ensures 0 <= result &*& result <= int_of_nat(n) &*& ! p(vs,result);
{
  switch(n) {
    case zero: return 0;
    case succ(n0):
      if( ! p(vs, int_of_nat(n))) {
        return int_of_nat(n);
      } else {
        int i = not_forall_nth_nat(vs, p, n0);
        return i;
      }
  }
}

lemma int not_forall_nth<t>(list<t> vs, fixpoint (list<t>, int, boolean) p)
  requires ! forall_nth(vs, p);
  ensures 0 <= result &*& result < length(vs) &*& ! p(vs, result);
{
   switch(vs) {
    case nil: return 0;
    case cons(h, t):
      int i = not_forall_nth_nat(vs, p, nat_of_int(length(vs) - 1));
      assert i <= int_of_nat(nat_of_int(length(vs) - 1));
      int_of_nat_of_int(length(vs) - 1);
      assert i <= length(vs) - 1;
      return i;
  }
}

lemma void forall_nth_elim_nat<t>(list<t> vs, fixpoint (list<t>, int, boolean) p, nat n, int i)
  requires forall_nth_core(vs, p, n) == true &*& 0 <= i && i <= int_of_nat(n);
  ensures p(vs, i) == true;
{
  switch(n) {
    case zero:
    case succ(n0):
      if(i == int_of_nat(n)) {
      } else {
          forall_nth_elim_nat(vs, p, n0, i);
      } 
  }
}

lemma void forall_nth_elim<t>(list<t> vs, fixpoint (list<t>, int, boolean) p, int i)
  requires forall_nth(vs, p) == true &*& 0 <= i &*& i < length(vs);
  ensures p(vs, i) == true;
{
  switch(vs) {
    case nil:
    case cons(h, t): forall_nth_elim_nat(vs, p, nat_of_int(length(vs) - 1), i);
  }
}

fixpoint boolean ok(int x, int y, int l, list<int> vs, int i) {
  return i < 0 || i >= l || nth(x + i, vs) == nth(y + i, vs);
}
@*/

class LCP {
 private final int[] a;
 private final int[] suffixes;
 private final int N;
 
 private int lcp(int[] a, int x, int y) 
   //@ requires array_slice<int>(a, 0, a.length, ?vs) &*& 0 <= x &*& x < a.length &*& 0 <= y &*& y < a.length;
   /*@ ensures array_slice<int>(a, 0, a.length, vs) &*&
               forall_nth(vs, (ok)(x, y, result)) == true &*& // forall i in (0:l) :: nth(x + i) == nth(y + i)
               (x + result < a.length - 1 && y + result < a.length -1 ? nth<int>(x +result, vs) != nth(y + result, vs) : true);
    @*/
 {
    int N = a.length;
    int l = 0;
    /*@
    if(! forall_nth(vs, (ok)(x, y, l))) {
      int i = not_forall_nth<int>(vs,  (ok)(x, y, l));
    }
    @*/
    while (x+l<N && y+l<N && a[x+l]==a[y+l])
      /*@ invariant array_slice(a, 0, a.length, vs) &*& 0 <= x+l &*& x+l <= a.length &*& 0 <= y + l &*& y + l <= a.length &*& 
                    forall_nth(vs, (ok)(x, y, l)) == true; @*/
      //@ decreases N - l;
    {
      l++;
      /*@
      if(! forall_nth(vs, (ok)(x, y, l))) {
        int i = not_forall_nth<int>(vs,  (ok)(x, y, l));
        forall_nth_elim(vs, (ok)(x, y, l - 1), i);
      }
      @*/
    }
    return l;
  }
}