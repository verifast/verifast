/*@

fixpoint int lcp<t>(list<t> xs, list<t> ys) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return
            switch (ys) {
                case nil: return 0;
                case cons(y, ys0): return x == y ? 1 + lcp(xs0, ys0) : 0;
            };
    }
}

@*/

int lcp(int a, int N, int x, int y)
    //@ requires [?f]array<int>(a, N, sizeof(int), integer, ?elems) &*& 0 <= x &*& x < N &*& 0 <= y &*& y < N;
    //@ ensures [f]array<int>(a, N, sizeof(int), integer, elems) &*& result == lcp(drop(x, elems), drop(y, elems));
{
    int l = 0;
    while (x + l < N && y + l < N && a[x+l] == a[y+l])
    {
        l++;
    }
    return l;
}
