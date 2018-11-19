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

@*/

int lcp(int a[], int N, int x, int y)
    //@ requires [?f]a[0..N] |-> ?elems &*& 0 <= x &*& x < N &*& 0 <= y &*& y < N;
    //@ ensures [f]a[0..N] |-> elems &*& result == lcp_(drop(x, elems), drop(y, elems));
{
    int l = 0;
    for (;;)
        /*@
        requires
            [f]a[0..N] |-> elems &*& 0 <= l &*& x + l <= N &*& y + l <= N;
        @*/
        /*@
        ensures 
            [f]a[0..N] |-> elems &*& l - old_l == lcp_(drop(x + old_l, elems), drop(y + old_l, elems));
        @*/
        //@ decreases N - l;
    {
        if (!(x + l < N && y + l < N && a[x+l] == a[y+l])) {
            /*@
            if (x + l == N) { drop_length(elems); }
            else if (y + l == N) { switch (drop(x + l, elems)) { case nil: case cons(h, t): } drop_length(elems); }
            else {
		    append_take_drop_n(elems, x + l);    
		    drop_n_plus_one(x + l, elems);
		    append_take_drop_n(elems, y + l);
		    drop_n_plus_one(y + l, elems);
            }
            @*/
            break;
        }
        //@ append_take_drop_n(elems, x + l);
        //@ drop_n_plus_one(x + l, elems);
        //@ append_take_drop_n(elems, y + l);
        //@ drop_n_plus_one(y + l, elems);
        //@ assert lcp_(drop(x + l, elems), drop(y + l, elems)) == 1 + lcp_(drop(x + l + 1, elems), drop(y + l + 1, elems));
        l++;
    }
    return l;
}
