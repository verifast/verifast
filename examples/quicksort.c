//@ #include <arrays.gh> // For ints_split and ints_join
//@ #include <quantifiers.gh> // For not_forall and forall_elim

/*@

fixpoint bool eq<t>(t x, t y) { return x == y; }

fixpoint int count_eq<t>(list<t> vs, t v) { return count(vs, (eq)(v)); }

fixpoint bool option_le(option<int> x, int y) {
    switch (x) {
        case none: return true;
        case some(x0): return x0 <= y;
    }
}

fixpoint bool option_le_option(option<int> x, option<int> y) {
    switch (y) {
        case none: return true;
        case some(y0): return option_le(x, y0);
    }
}

fixpoint bool is_sorted_between(option<int> lower, list<int> vs, option<int> upper) {
    switch (vs) {
        case nil: return option_le_option(lower, upper);
        case cons(v, vs0): return option_le(lower, v) && is_sorted_between(some(v), vs0, upper);
    }
}

fixpoint bool le(int x, int y) { return x <= y; }
fixpoint bool ge(int x, int y) { return x >= y; }

fixpoint int mplus<t>(fixpoint(t, int) M1, fixpoint(t, int) M2, t x) { return M1(x) + M2(x); }

fixpoint int memp<t>(t x) { return 0; }

lemma a fixpoint_neq_elim<a, b>(fixpoint(a, b) f, fixpoint(a, b) g);
    requires f != g;
    ensures f(result) != g(result);

lemma_auto void count_eq_nil_eq_memp<t>()
    requires true;
    ensures (count_eq)(nil) == memp;
{
    if ((count_eq)(nil) != memp) {
        t x = fixpoint_neq_elim((count_eq)(nil), memp);
    }
}

lemma_auto void mplus_memp_l<t>(fixpoint(t, int) M)
    requires true;
    ensures (mplus)(memp, M) == M;
{
    if ((mplus)(memp, M) != M) {
        t x = fixpoint_neq_elim((mplus)(memp, M), M);
    }
}

lemma void count_eq_append<t>(list<t> xs, list<t> ys)
    requires true;
    ensures (count_eq)(append(xs, ys)) == (mplus)((count_eq)(xs), (count_eq)(ys));
{
    if ((count_eq)(append(xs, ys)) != (mplus)((count_eq)(xs), (count_eq)(ys))) {
        t x = fixpoint_neq_elim((count_eq)(append(xs, ys)), (mplus)((count_eq)(xs), (count_eq)(ys)));
        count_append(xs, ys, (eq)(x));
    }
}

@*/

void swap (int *a, int i, int j)
  //@ requires a[i] |-> ?vi &*& a[j] |-> ?vj;
  //@ ensures a[i] |-> vj &*& a[j] |-> vi;
{
  int aj = a[j];
  a[j] = a[i];
  a[i] = aj;
}

int partition(int *a, int lo, int hi)
  //@ requires a[lo..hi + 1] |-> ?vs &*& lo <= hi;
  /*@
  ensures
      a[lo..result] |-> ?vslow &*&
      a[result] |-> ?vpivot &*&
      a[result + 1..hi + 1] |-> ?vshigh &*&
      forall(vslow, (ge)(vpivot)) == true &*&
      forall(vshigh, (le)(vpivot)) == true &*&
      (mplus)((count_eq)(vslow), (count_eq)(cons(vpivot, vshigh))) == (count_eq)(vs);
  @*/
{
  //@ ints_split(a + lo, hi - lo);
  int pivot = *(a+hi);
  //@ assert a[lo..hi] |-> ?vstodo0 &*& a[hi..hi + 1] |-> cons(_, ?vsrest);
  //@ switch (vsrest) { case nil: case cons(h, t): }
  int i = lo - 1;
  int j;
  //@ count_eq_append(vstodo0, {pivot});
  //@ assert vs == append(vstodo0, {pivot});
  for (j = lo; j < hi; j++)
    /*@
    invariant
      a[lo..i + 1] |-> ?vslow &*&
      a[i + 1..j] |-> ?vshigh &*&
      a[j..hi] |-> ?vstodo &*&
      forall(vslow, (ge)(pivot)) == true &*&
      forall(vshigh, (le)(pivot)) == true &*&
      (mplus)((count_eq)(vstodo), (mplus)((count_eq)(vslow), (count_eq)(cons(pivot, vshigh)))) == (count_eq)(vs);
    @*/
  {
    
    int aj = *(a + j);
    if (aj < pivot) {
      i++;
      if (i < j) {
        swap(a, i, j);
        //@ int ai = a[j];
        //@ close ints(a + i, 1, {aj});
        //@ ints_join(a + lo);
        //@ close ints(a + j, 1, {ai});
        //@ ints_join(a + i + 1);
        //@ forall_append(vslow, {aj}, (ge)(pivot));
        //@ forall_append(tail(vshigh), {ai}, (le)(pivot));
        /*@
        if ((mplus)((count_eq)(tail(vstodo)), (mplus)((count_eq)(append(vslow, {aj})), (count_eq)(cons(pivot, append(tail(vshigh), {ai}))))) !=
            (mplus)((count_eq)(vstodo), (mplus)((count_eq)(vslow), (count_eq)(cons(pivot, vshigh))))) {
            int x = fixpoint_neq_elim((mplus)((count_eq)(tail(vstodo)), (mplus)((count_eq)(append(vslow, {aj})), (count_eq)(cons(pivot, append(tail(vshigh), {ai}))))),
                                    (mplus)((count_eq)(vstodo), (mplus)((count_eq)(vslow), (count_eq)(cons(pivot, vshigh)))));
            count_append(vslow, {aj}, (eq)(x));
            count_append(tail(vshigh), {ai}, (eq)(x));
            assert false;
        }
        @*/
      } else {
        //@ assert i == j;
        //@ open ints(a + i, 0, _);
        //@ close ints(a + i, 1, _);
        //@ ints_join(a + lo);
        //@ forall_append(vslow, {aj}, (ge)(pivot));
        /*@
        if ((mplus)((count_eq)(tail(vstodo)), (mplus)((count_eq)(append(vslow, {aj})), (count_eq)({pivot}))) !=
            (mplus)((count_eq)(vstodo), (mplus)((count_eq)(vslow), (count_eq)(cons(pivot, vshigh))))) {
            int x = fixpoint_neq_elim((mplus)((count_eq)(tail(vstodo)), (mplus)((count_eq)(append(vslow, {aj})), (count_eq)({pivot}))),
                                    (mplus)((count_eq)(vstodo), (mplus)((count_eq)(vslow), (count_eq)(cons(pivot, vshigh)))));
            count_append(vslow, {aj}, (eq)(x));
            assert false;
        }
        @*/
      }
    } else {
      //@ close ints(a + j, 1, {aj});
      //@ ints_join(a + i + 1);
      //@ forall_append(vshigh, {aj}, (le)(pivot));
      /*@
      if ((mplus)((count_eq)(tail(vstodo)), (mplus)((count_eq)(vslow), (count_eq)(cons(pivot, append(vshigh, {aj}))))) !=
          (mplus)((count_eq)(vstodo), (mplus)((count_eq)(vslow), (count_eq)(cons(pivot, vshigh))))) {
          int x = fixpoint_neq_elim((mplus)((count_eq)(tail(vstodo)), (mplus)((count_eq)(vslow), (count_eq)(cons(pivot, append(vshigh, {aj}))))),
                                  (mplus)((count_eq)(vstodo), (mplus)((count_eq)(vslow), (count_eq)(cons(pivot, vshigh)))));
          count_append(vshigh, {aj}, (eq)(x));
          assert false;
      }
      @*/
    }
  }
  //@ assert j == hi;
  //@ open ints(a + hi, 0, _);
  i++;
  //@ assert a[lo..i] |-> ?vslow &*& a[i..hi] |-> ?vshigh;
  if (i < hi) {
    swap(a, i, hi);
    //@ int ai = a[hi];
    //@ close ints(a + hi, 1, {ai});
    //@ ints_join(a + i + 1);
    //@ forall_append(tail(vshigh), {ai}, (le)(pivot));
      /*@
      if ((mplus)((count_eq)(vslow), (count_eq)(cons(pivot, append(tail(vshigh), {ai})))) !=
          (mplus)((count_eq)(nil), (mplus)((count_eq)(vslow), (count_eq)(cons(pivot, vshigh))))) {
          int x = fixpoint_neq_elim((mplus)((count_eq)(vslow), (count_eq)(cons(pivot, append(tail(vshigh), {ai})))),
                                  (mplus)((count_eq)(nil), (mplus)((count_eq)(vslow), (count_eq)(cons(pivot, vshigh)))));
          count_append(tail(vshigh), {ai}, (eq)(x));
          assert false;
      }
      @*/
  } else {
      //@ assert i == hi;
      //@ open ints(a + hi, 0, _);
  }
  return i;
}

/*@

lemma void is_sorted_forall_le(int lower, list<int> vs)
    requires is_sorted_between(none, vs, none) && forall(vs, (le)(lower));
    ensures is_sorted_between(some(lower), vs, none) == true;
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
    }
}

lemma void is_sorted_forall_ge(option<int> lower, list<int> vs, int upper)
    requires is_sorted_between(lower, vs, none) && forall(vs, (ge)(upper)) && option_le(lower, upper);
    ensures is_sorted_between(lower, vs, some(upper)) == true;
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
            is_sorted_forall_ge(some(v), vs0, upper);
    }
}

lemma void mem_count_eq<t>(t x, list<t> xs)
    requires true;
    ensures mem(x, xs) == (count_eq(xs, x) > 0);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                count_nonnegative(xs0, (eq)(x));
            } else {
                mem_count_eq(x, xs0);
            }
    }
}

lemma void note(bool b)
    requires b;
    ensures b;
{}

lemma void count_eq_forall<t>(list<t> xs, list<t> ys, fixpoint(t, bool) p)
    requires forall(xs, p) == true &*& (count_eq)(ys) == (count_eq)(xs);
    ensures forall(ys, p) == true;
{
    if (!forall(ys, p)) {
        t x = not_forall(ys, p);
        mem_count_eq(x, ys);
        mem_count_eq(x, xs);
        note((count_eq)(xs)(x) > 0);
        assert mem(x, xs) == true;
        forall_elim(xs, p, x);
        assert false;
    }
}

lemma void is_sorted_append(option<int> lower, list<int> xs, int pivot, list<int> ys)
    requires is_sorted_between(lower, xs, some(pivot)) && is_sorted_between(some(pivot), ys, none);
    ensures is_sorted_between(lower, append(xs, ys), none) == true;
{
    switch (xs) {
        case nil:
            switch (lower) { case none: case some(l): }
            switch (ys) { case nil: case cons(h, t): }
        case cons(x, xs0):
            is_sorted_append(some(x), xs0, pivot, ys);
    }
}

@*/

void quicksort(int *a, int lo, int hi)
  //@ requires a[lo..hi + 1] |-> ?vs;
  //@ ensures a[lo..hi + 1] |-> ?vs2 &*& (count_eq)(vs2) == (count_eq)(vs) &*& is_sorted_between(none, vs2, none) == true;
{
  if (lo > hi) {
    //@ switch (vs) { case nil: case cons(v0, vs0): }
    return;
  } else {
    int p = partition(a, lo, hi);
    //@ assert a[lo..p] |-> ?vslow0 &*& a[p] |-> ?pivot &*& a[p + 1..hi + 1] |-> ?vshigh0;
    //@ assert (mplus)((count_eq)(vslow0), (count_eq)(cons(pivot, vshigh0))) == (count_eq)(vs);
    //@ count_eq_append({pivot}, vshigh0);
    quicksort(a, lo, p-1);
    quicksort(a, p+1, hi);
    //@ assert a[lo..p] |-> ?vslow &*& a[p] |-> pivot &*& a[p + 1..hi + 1] |-> ?vshigh;
    //@ close ints(a + p, hi + 1 - p, _);
    //@ ints_join(a + lo);
    //@ assert a[lo..hi + 1] |-> ?vs2;
    //@ assert vs2 == append(vslow, cons(pivot, vshigh));
    //@ assert (count_eq)(vslow) == (count_eq)(vslow0);
    //@ count_eq_append(vslow, cons(pivot, vshigh));
    //@ count_eq_append({pivot}, vshigh);
    
    //@ count_eq_forall(vslow0, vslow, (ge)(pivot));
    //@ is_sorted_forall_ge(none, vslow, pivot);
    //@ assert is_sorted_between(none, vslow, some(pivot)) == true;
    
    //@ count_eq_forall(vshigh0, vshigh, (le)(pivot));
    //@ is_sorted_forall_le(pivot, vshigh);
    //@ is_sorted_append(none, vslow, pivot, cons(pivot, vshigh));
  }
}
