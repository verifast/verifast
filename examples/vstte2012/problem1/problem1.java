/*
The specification below proves:
  1. safety (no array indexing errors)
  2. termination (via loop decreases: j - i + 1)
  3. behavior 
    (a) the resulting array is sorted (postcondition: is_sorted(vs2))
    (b) the resulting array is a permutation of the original array (postcondition: is_perm(vs, vs2))
*/

/*@

lemma_auto void length_append_auto<t>(list<t> xs, list<t> ys)
    requires true;
    ensures length(append(xs, ys)) == length(xs) + length(ys);
{
    length_append(xs, ys);
}

lemma_auto void length_take_n_auto<t>(int n, list<t> xs)
    requires 0 <= n && n <= length(xs);
    ensures length(take(n, xs)) == n;
{
    length_take_n(n, xs);
}

fixpoint boolean is_sorted(list<boolean> vs) {
  switch(vs) {
    case nil: return true;
    case cons(h, t):
      return switch(t) { 
        case nil: return true; 
        case cons(h0, t0): return (h == false || h0 == true) && is_sorted(t);
      };
  }
}

lemma void is_sorted_lemma(list<boolean> vs, int i)
  requires 0 <= i && i <= length(vs) &*& all_eq(take(i, vs), false) == true &*& all_eq(drop(i, vs), true) == true;
  ensures is_sorted(vs) == true;
{
  switch(vs) {
    case nil:
    case cons(h, t):
      switch(t) {
        case nil:
        case cons(h0, t0):
          if(i == 0) {
            is_sorted_lemma(t, 0);
          } else {
            is_sorted_lemma(t, i -1);
          }
      }
  }
}

lemma void update_drop<t>(list<t> xs, int i, t v, int j)
  requires 0 <= i && i < length(xs) &*& 0 <= j &*& i < j;
  ensures drop(j, update(i, v, xs)) == drop(j, xs);
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i == 0) {
      } else {
        update_drop(t, i - 1, v, j - 1);
      }
  }
}

fixpoint list<t> execute_swaps<t>(list<pair<int, int> > swaps, list<t> xs) {
  switch(swaps) {
    case nil: return xs;
    case cons(h, t):
      return switch(h) {
        case pair(i, j): return update(j, nth(i, execute_swaps(t, xs)), update(i, nth(j,  execute_swaps(t, xs)), execute_swaps(t, xs)));
      };
  }
}

predicate is_perm<t>(list<t> xs, list<t> ys) =
  exists<list<pair<int, int> > >(?swaps) &*& execute_swaps(swaps, xs) == ys;
@*/

class Problem1 {
  static void swap(boolean[] a, int i, int j) 
    //@ requires array_slice(a, 0, a.length, ?vs) &*& 0 <= i &*& i < a.length &*& 0 <= j &*& j < a.length;
    //@ ensures array_slice(a, 0, a.length, update(j, nth(i, vs), update(i, nth(j, vs), vs)));
  {
    boolean tmp = a[i];
    a[i] = a[j];
    a[j] = tmp;
  }
  
  static void two_way_sort(boolean[] a) 
    //@ requires array_slice(a, 0, a.length, ?vs);
    //@ ensures array_slice(a, 0, a.length, ?vs2) &*& is_sorted(vs2) == true &*& is_perm(vs, vs2);
  {
    int i = 0;
    int j = a.length - 1;
    //@ close exists(nil);
    //@ close is_perm(vs, vs);
    while(i <= j) 
      /*@ invariant 0 <= i && i <= a.length &*& -1 <= j &*& j < a.length &*& j - i >= -1 &*&
          array_slice(a, 0, a.length, ?xs) &*& 
          all_eq(take(i, xs), false) == true &*&
          all_eq(drop(j + 1, xs), true) == true &*&
          is_perm(vs, xs); 
          @*/
      //@ decreases j - i + 1;
    {
      if(! a[i]) {
        //@ take_one_more(i, xs);
        i++;
      } else if (a[j]) {
        //@ drop_n_plus_one(j, xs);
        j--;
      } else {
        swap(a, i, j);
        //@ assert array_slice(a, 0, a.length, ?ys);
        //@ open is_perm(vs, xs);
        //@ open exists(?swaps);
        //@ close exists(cons(pair(i, j), swaps));
        //@ close is_perm(vs, ys);
        //@ take_one_more(i, ys);
        //@ drop_n_plus_one(j, ys);
        //@ update_drop(xs, i, nth(j, xs), j+1);
        i++;       
        j--;
      }
    }
    //@ is_sorted_lemma(xs, i);
  }
}