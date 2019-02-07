/*@

// Definition of minimum of a list of values.

fixpoint int min0(int x, list<int> xs) {
    switch (xs) {
        case nil: return x;
        case cons(x1, xs1): return min0(x1 < x ? x1 : x, xs1);
    }
}

fixpoint int min(list<int> xs) {
    return min0(head(xs), tail(xs));
}

lemma void min0_append(int x, list<int> xs1, list<int> xs2)
    requires true;
    ensures min0(x, append(xs1, xs2)) == min0(min0(x, xs1), xs2);
{
    switch (xs1) {
        case nil:
        case cons(x1, xs11):
            min0_append(x1 < x ? x1 : x, xs11, xs2);
    }
}

// Definition of the relation "list A is a permutation of list B"

fixpoint list<t> do_swap<t>(pair<int, int> swap, list<t> xs) {
    switch (swap) {
        case pair(i, j): return 0 <= i && i <= j && j < length(xs) ? update(i, nth(j, xs), update(j, nth(i, xs), xs)) : xs;
    }
}

fixpoint list<t> do_swaps<t>(list<pair<int, int> > swaps, list<t> xs) {
    switch (swaps) {
        case nil: return xs;
        case cons(swap, swaps0): return do_swap(swap, do_swaps(swaps0, xs));
    }
}

predicate permut<t>(list<t> xs, list<pair<int, int> > swaps; list<t> ys) = ys == do_swaps(swaps, xs);

// Some lemmas about the interaction between list update, append, and take. (Applied automatically; should be in the VeriFast library.)

lemma_auto void update_append_r<t>(int i, t v, list<t> xs, list<t> ys)
    requires length(xs) <= i && i < length(xs) + length(ys);
    ensures update(i, v, append(xs, ys)) == append(xs, update(i - length(xs), v, ys));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            update_append_r(i - 1, v, xs0, ys);
    }
}

lemma_auto void update_append_l<t>(int i, t v, list<t> xs, list<t> ys)
    requires 0 <= i && i < length(xs);
    ensures update(i, v, append(xs, ys)) == append(update(i, v, xs), ys);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (i == 0) {
            } else {
                update_append_l(i - 1, v, xs0, ys);
            }
    }
}

lemma_auto void update_take<t>(int i, t v, int n, list<t> xs)
    requires 0 <= i && i < n && n <= length(xs);
    ensures update(i, v, take(n, xs)) == take(n, update(i, v, xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (i == 0) {
            } else {
                update_take(i - 1, v, n - 1, xs0);
            }
    }
}

@*/

class Bag {
  
  int[] a;
  int n;
  
  //@ predicate valid(list<int> elems) = a |-> ?a &*& n |-> ?n &*& array_slice(a, 0, n, elems);
  
  Bag(int[] input)
    //@ requires array_slice(input, 0, input.length, ?xs);
    //@ ensures valid(xs);
  {
    n = input.length;
    a = new int[n];

    // Some magic to deal with System.arraycopy's polymorphism over the array element type.
    //@ close array_slice_dynamic(array_slice_int, input, 0, n, _);
    //@ close array_slice_dynamic(array_slice_int, a, 0, n, _);
    //@ close arraycopy_pre(array_slice_int, false, 1, input, 0, n, _, a, 0);
    System.arraycopy(input, 0, a, 0, n);
    //@ open arraycopy_post(_, _, _, _, _, _, _, _, _);
    //@ open array_slice_dynamic(_, a, _, _, _);
  }
  
  int extractMin()
    //@ requires valid(?xs) &*& xs != nil;
    /*@
    ensures
        valid(?xs1) &*& result == min(xs) &*&
        permut(xs, _, append(xs1, cons(result, nil))); // The new elements plus the result are a permutation of the old elements.
    @*/
  {
    int mindex = 0;
    //@ switch (xs) { case nil: case cons(x0, xs0): }
    int m = a[mindex];
    for (int i = 1; i < n; i++)
      /*@
      invariant
        a |-> ?ar &*& n |-> ?num &*& array_slice(ar, 0, num, xs) &*&
        0 <= mindex &*& mindex < num &*&
        1 <= i &*& i <= num &*&
        nth(mindex, xs) == m &*& m == min(take(i, xs));
      @*/
    {
      //@ take_one_more(i, xs);
      //@ min0_append(head(take(i, xs)), take(i, xs), cons(nth(i, xs), nil));
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    return m;
    //@ assert a |-> ?array &*& n |-> ?number &*& array_slice(array, 0, number, ?xs1);
    //@ assert xs == append(take(number, xs), drop(number, xs));
    //@ assert drop(number, xs) == cons(?nv, ?tail);
    //@ switch (tail) { case nil: case cons(h, t): length_nonnegative(t); }
    /*@
    if (mindex < number) {
        update_append_l(mindex, nv, take(number, xs), cons(m, nil));
    }
    @*/
    //@ close permut(xs, cons(pair(mindex, number), nil), append(xs1, cons(m, nil)));
  }
  
} 