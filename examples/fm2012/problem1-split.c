//@ #include "arrays.gh"

/*@

fixpoint int lcp_<t>(list<t> xs, list<t> ys) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return
            switch (ys) {
                case nil: return 0;
                case cons(y, ys0): return x == y ? 1 + lcp_(xs0, ys0) : 0;
            };
    }
}

lemma void ints_split_exact(real f, int *a, int N, int l)
    requires [f]a[0..N] |-> ?vs &*& 0 <= l &*& l <= N;
    ensures [f]a[0..l] |-> take(l, vs) &*& [f]a[l..N] |-> drop(l, vs);
{
    ints_split(a, l);
}

lemma void ints_join_exact(int *a, int m)
    requires [?f]a[0..m] |-> ?vs1 &*& [f]ints(a + m, ?n, ?vs2);
    ensures [f]a[0..m + n] |-> append(vs1, vs2);
{
    ints_join(a);
}

@*/

int lcp(int *a, int N, int x, int y)
    //@ requires [?f]a[0..N] |-> ?elems &*& 0 <= x &*& x < N &*& 0 <= y &*& y < N;
    //@ ensures [f]a[0..N] |-> elems &*& result == lcp_(drop(x, elems), drop(y, elems));
{
    //@ ints_split_exact(f/2, a, N, x);
    //@ ints_split_exact(f/2, a, N, y);
    int l = 0;
    for (;;)
        /*@
        requires
            [f/2]a[x + l..N] |-> ?xs &*& [f/2]a[y + l..N] |-> ?ys &*& 0 <= l &*& l <= N;
        @*/
        /*@
        ensures 
            [f/2]a[x + old_l..N] |-> xs &*& [f/2]a[y + old_l..N] |-> ys &*&
            l - old_l == lcp_(xs, ys);
        @*/
        //@ decreases N - l;
    {
        //@ open [_]ints(a + x + l, _, _);
        //@ open [_]ints(a + y + l, _, _);
        if (!(x + l < N && y + l < N && a[x + l] == a[y + l])) {
            break;
        }
        l++;
    }
    //@ ints_join_exact(a, x);
    //@ ints_join_exact(a, y);
    return l;
}
