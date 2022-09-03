#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"

int read_int()
    //@ requires true;
    //@ ensures true;
{
    int x;
    scanf("%i", &x);
    return x;
}

/*@

fixpoint bool is_sorted_between(int l, list<int> xs, int u) {
    switch (xs) {
        case nil: return l <= u;
        case cons(x, xs0): return l <= x && is_sorted_between(x, xs0, u);
    }
}

fixpoint list<int> insert_sorted(int x, list<int> xs) {
    switch (xs) {
        case nil: return cons(x, nil);
        case cons(x0, xs0): return x0 < x ? cons(x0, insert_sorted(x, xs0)) : cons(x, xs);
    }
}

fixpoint list<int> sorted(list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return insert_sorted(x, sorted(xs0));
    }
}

fixpoint int count_eq<t>(t x, list<t> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x0, xs0): return (x0 == x ? 1 : 0) + count_eq(x, xs0);
    }
}

fixpoint bool same_count<t>(list<t> xs, list<t> ys, t x) { return count_eq(x, xs) == count_eq(x, ys); }

fixpoint bool is_permutation<t>(fixpoint(fixpoint(t, bool), bool) forall_t, list<t> xs, list<t> ys) { return forall_t((same_count)(xs, ys)); }

lemma void count_insert_sorted(int x, int y, list<int> xs)
    requires true;
    ensures count_eq(x, insert_sorted(y, xs)) == count_eq(x, cons(y, xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            count_insert_sorted(x, y, xs0);
    }
}

lemma void count_sorted(int x, list<int> xs)
    requires true;
    ensures count_eq(x, sorted(xs)) == count_eq(x, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            count_sorted(x, xs0);
            count_insert_sorted(x, x0, sorted(xs0));
    }
}

lemma void is_permutation_sorted(list<int> xs)
    requires true;
    ensures is_permutation(forall_int, sorted(xs), xs) == true;
{
    if (!is_permutation(forall_int, sorted(xs), xs)) {
        get_forall_int();
        int x = not_forall_t(forall_int, (same_count)(sorted(xs), xs));
        count_sorted(x, xs);
    }
}

lemma void insert_sorted_commut(int x, int y, list<int> xs)
    requires true;
    ensures insert_sorted(x, insert_sorted(y, xs)) == insert_sorted(y, insert_sorted(x, xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            insert_sorted_commut(x, y, xs0);
    }
}

lemma void insert_sorted_append_cons(int x, list<int> ys, list<int> xs)
    requires true;
    ensures sorted(append(ys, cons(x, xs))) == insert_sorted(x, sorted(append(ys, xs)));
{
    switch (ys) {
        case nil:
        case cons(y, ys0):
            assert sorted(append(ys, cons(x, xs))) == insert_sorted(y, sorted(append(ys0, cons(x, xs))));
            insert_sorted_append_cons(x, ys0, xs);
            assert sorted(append(ys, cons(x, xs))) == insert_sorted(y, insert_sorted(x, sorted(append(ys0, xs))));
            insert_sorted_commut(x, y, sorted(append(ys0, xs)));
    }
}

lemma void sorted_append_flip(list<int> xs, list<int> ys)
    requires true;
    ensures sorted(append(xs, ys)) == sorted(append(ys, xs));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            assert sorted(append(xs, ys)) == insert_sorted(x, sorted(append(xs0, ys)));
            sorted_append_flip(xs0, ys);
            assert sorted(append(xs, ys)) == insert_sorted(x, sorted(append(ys, xs0)));
            insert_sorted_append_cons(x, ys, xs0);
    }
}

lemma void sorted_append_insert_sorted(int x, list<int> xs, list<int> ys)
    requires true;
    ensures sorted(append(insert_sorted(x, xs), ys)) == insert_sorted(x, sorted(append(xs, ys)));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 < x) {
                assert sorted(append(insert_sorted(x, xs), ys)) == sorted(append(cons(x0, insert_sorted(x, xs0)), ys));
                assert sorted(append(insert_sorted(x, xs), ys)) == insert_sorted(x0, sorted(append(insert_sorted(x, xs0), ys)));
                sorted_append_insert_sorted(x, xs0, ys);
                assert sorted(append(insert_sorted(x, xs), ys)) == insert_sorted(x0, insert_sorted(x, sorted(append(xs0, ys))));
                insert_sorted_commut(x0, x, sorted(append(xs0, ys)));
                assert sorted(append(insert_sorted(x, xs), ys)) == insert_sorted(x, insert_sorted(x0, sorted(append(xs0, ys))));
            } else {
                assert sorted(append(insert_sorted(x, xs), ys)) == insert_sorted(x, sorted(append(xs, ys)));
            }
    }
}

lemma void sorted_sorted(list<int> xs)
    requires true;
    ensures sorted(sorted(xs)) == sorted(xs);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            sorted_append_insert_sorted(x, sorted(xs0), nil);
            assert sorted(insert_sorted(x, sorted(xs0))) == insert_sorted(x, sorted(sorted(xs0)));
            sorted_sorted(xs0);
    }
}

lemma void sorted_append_sorted(list<int> xs, list<int> ys)
    requires true;
    ensures sorted(append(sorted(xs), sorted(ys))) == sorted(append(xs, ys));
{
    switch (xs) {
        case nil:
            sorted_sorted(ys);
        case cons(x0, xs0):
            assert sorted(append(sorted(xs), sorted(ys))) == sorted(append(insert_sorted(x0, sorted(xs0)), sorted(ys)));
            sorted_append_insert_sorted(x0, sorted(xs0), sorted(ys));
            assert sorted(append(sorted(xs), sorted(ys))) == insert_sorted(x0, sorted(append(sorted(xs0), sorted(ys))));
            sorted_append_sorted(xs0, ys);
            assert sorted(append(sorted(xs), sorted(ys))) == insert_sorted(x0, sorted(append(xs0, ys)));
            
    }
}

lemma void insert_sorted_is_sorted(int l, int x, list<int> xs, int u)
    requires l <= x &*& x <= u &*& is_sorted_between(l, xs, u) == true;
    ensures is_sorted_between(l, insert_sorted(x, xs), u) == true;
{
    switch (xs) {
        case nil:
            
        case cons(x0, xs0):
            if (x0 < x) {
                insert_sorted_is_sorted(x0, x, xs0, u);
            }
    }
}

lemma void sorted_is_sorted(list<int> xs)
    requires forall(xs, int_within_limits) == true;
    ensures is_sorted_between(INT_MIN, sorted(xs), INT_MAX) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            sorted_is_sorted(xs0);
            insert_sorted_is_sorted(INT_MIN, x, sorted(xs0), INT_MAX);
    }
}

fixpoint int min(int x, int y) { return x < y ? x : y; }

lemma void is_sorted_weaken(int l1, int l0, list<int> xs, int r0, int r1)
    requires l1 <= l0 &*& is_sorted_between(l0, xs, r0) == true &*& r0 <= r1;
    ensures is_sorted_between(l1, xs, r1) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            is_sorted_weaken(x, x, xs0, r0, r1);
    }
}

lemma void is_sorted_limits(int l, int x, list<int> xs, int u)
    requires is_sorted_between(l, cons(x, xs), u) == true;
    ensures x <= u;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            is_sorted_limits(x0, x0, xs0, u);
    }
}

lemma void is_sorted_sorted(int l, list<int> xs)
    requires is_sorted_between(l, xs, INT_MAX) == true;
    ensures is_sorted_between(l, sorted(xs), INT_MAX) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            is_sorted_sorted(x, xs0);
            is_sorted_limits(l, x, xs0, INT_MAX);
            is_sorted_weaken(l, x, sorted(xs0), INT_MAX, INT_MAX);
            insert_sorted_is_sorted(l, x, sorted(xs0), INT_MAX);
    }
}

lemma void sorted_append_is_sorted(int lxs, list<int> xs, int lys, list<int> ys)
    requires is_sorted_between(lxs, xs, INT_MAX) == true &*& is_sorted_between(lys, ys, INT_MAX) == true;
    ensures is_sorted_between(min(lxs, lys), sorted(append(xs, ys)), INT_MAX) == true;
{
    switch (xs) {
        case nil:
            is_sorted_sorted(lys, ys);
            is_sorted_weaken(min(lxs, lys), lys, sorted(ys), INT_MAX, INT_MAX);
        case cons(x, xs0):
            is_sorted_limits(lxs, x, xs0, INT_MAX);
            sorted_append_is_sorted(x, xs0, lys, ys);
            is_sorted_weaken(min(lxs, lys), min(x, lys), sorted(append(xs0, ys)), INT_MAX, INT_MAX);
            insert_sorted_is_sorted(min(lxs, lys), x, sorted(append(xs0, ys)), INT_MAX);
    }
}

lemma void is_sorted_insert_sorted(int x, list<int> xs)
    requires is_sorted_between(x, xs, INT_MAX) == true;
    ensures insert_sorted(x, xs) == cons(x, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
    }
}

@*/

void merge_sort_core(int *pxs, int *pys, int n)
    //@ requires pxs[0..n] |-> ?vs &*& pys[0..n] |-> _;
    //@ ensures pxs[0..n] |-> sorted(vs) &*& pys[0..n] |-> _;
{
    //@ if (n < 2) { switch (vs) { case nil: case cons(v, vs0): switch (vs0) { case nil: case cons(v0, vs00): } } }
    if (n >= 2) {
        int *left = pxs;
        int nleft = n / 2;
        //@ div_rem(n, 2);
        //@ ints_limits(pxs);
        //@ case_split_sizeof_int();
        int *right = pxs + nleft;
        int nright = n - n / 2;
        //@ ints_split(pxs, nleft);
        //@ ints__split(pys, nright);
        //@ assert left[0..nleft] |-> ?ls0 &*& right[0..nright] |-> ?rs0;
        //@ ints_limits(left);
        //@ ints_limits(right);
        //@ ints__split(pys, nleft);
        merge_sort_core(left, pys, nleft);
        //@ ints__join(pys);
        merge_sort_core(right, pys, nright);
        //@ ints__join(pys);
        //@ sorted_is_sorted(ls0);
        //@ sorted_is_sorted(rs0);
        int i = 0;
        int j = 0;
        int k = 0;
        for (;;)
            /*@
            requires
                left[i..nleft] |-> ?ls &*& right[j..nright] |-> ?rs &*& pys[k..n] |-> _ &*& n - k == nleft - i + nright - j &*&
                is_sorted_between(INT_MIN, ls, INT_MAX) == true &*& is_sorted_between(INT_MIN, rs, INT_MAX) == true;
            @*/
            /*@
            ensures
                left[old_i..nleft] |-> _ &*& right[old_j..nright] |-> _ &*& pys[old_k..n] |-> sorted(append(ls, rs));
            @*/
        {
            //@ ints_limits(left + i);
            //@ ints_limits(right + j);
            //@ open ints(left + i, _, _);
            //@ open ints(right + j, _, _);
            //@ open ints_(pys + k, _, _);
            if (i == nleft) {
                if (j == nright) {
                    break;
                } else {
                    pys[k] = right[j];
                    j++;
                    k++;
                    //@ is_sorted_weaken(INT_MIN, head(rs), tail(rs), INT_MAX, INT_MAX);
                    //@ assert sorted(rs) == insert_sorted(head(rs), sorted(tail(rs)));
                    //@ is_sorted_sorted(head(rs), tail(rs));
                    //@ is_sorted_insert_sorted(head(rs), sorted(tail(rs)));
                    //@ assert cons(head(rs), sorted(tail(rs))) == sorted(rs);
                }
            } else {
                //@ is_sorted_weaken(INT_MIN, head(ls), tail(ls), INT_MAX, INT_MAX);
                if (j == nright) {
                    pys[k] = left[i];
                    i++;
                    k++;
                    //@ is_sorted_sorted(head(ls), tail(ls));
                    //@ is_sorted_insert_sorted(head(ls), sorted(tail(ls)));
                } else {
                    //@ is_sorted_weaken(INT_MIN, head(rs), tail(rs), INT_MAX, INT_MAX);
                    if (left[i] <= right[j]) {
                        pys[k] = left[i];
                        i++;
                        k++;
                        //@ sorted_append_is_sorted(head(ls), tail(ls), head(rs), rs);
                        //@ is_sorted_insert_sorted(head(ls), sorted(append(tail(ls), rs)));
                        //@ assert cons(head(ls), sorted(append(tail(ls), rs))) == sorted(append(ls, rs));
                    } else {
                        pys[k] = right[j];
                        j++;
                        k++;
                        //@ sorted_append_is_sorted(head(rs), tail(rs), head(ls), ls);
                        //@ is_sorted_insert_sorted(head(rs), sorted(append(tail(rs), ls)));
                        //@ sorted_append_flip(ls, rs);
                        //@ assert sorted(append(ls, rs)) == sorted(append(rs, ls));
                        //@ assert sorted(append(ls, rs)) == insert_sorted(head(rs), sorted(append(tail(rs), ls)));
                        //@ assert sorted(append(ls, rs)) == cons(head(rs), sorted(append(tail(rs), ls)));
                        //@ sorted_append_flip(ls, tail(rs));
                    }
                }
            }
        }
        //@ ints__join(pxs);
        for (int p = 0; ;)
            //@ requires pys[p..n] |-> ?ys &*& pxs[p..n] |-> _ &*& p <= n;
            //@ ensures pxs[old_p..n] |-> ys &*& pys[old_p..n] |-> _;
        {
            //@ open ints(pys + p, _, _);
            //@ open ints_(pxs + p, _, _);
            if (p >= n) break;
            pxs[p] = pys[p];
            p++;
            
        }
        //@ sorted_append_sorted(ls0, rs0);
    }
}

void merge_sort(int *pxs, int n)
    //@ requires pxs[0..n] |-> ?vs &*& n <= 15000;
    //@ ensures pxs[0..n] |-> sorted(vs);
{
    //@ case_split_sizeof_int();
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    merge_sort_core(pxs, pys, n);
    free(pys);
}

/*@

lemma void is_sorted_between_index_of(list<int> vs, int x, int i)
    requires 0 <= i &*& i < length(vs) &*& nth(i, vs) == x &*& is_sorted_between(INT_MIN - 1, take(i, vs), x - 1) == true;
    ensures index_of(x, vs) == i;
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
            if (v == x) {
                if (i != 0) {
                    is_sorted_limits(INT_MIN - 1, v, take(i - 1, vs0), x - 1);
                }
            } else {
                is_sorted_weaken(INT_MIN - 1, v, take(i - 1, vs0), x - 1, x - 1);
                is_sorted_between_index_of(vs0, x, i - 1);
            }
    }
}

lemma void is_sorted_nth_neq_eq(list<int> vs, int k, int x)
    requires is_sorted_between(INT_MIN, vs, INT_MAX) == true &*& 0 < k &*& k < length(vs) &*& nth(k - 1, vs) != x &*& nth(k, vs) == x;
    ensures is_sorted_between(INT_MIN - 1, take(k, vs), x - 1) == true;
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
            switch (vs0) {
                case nil:
                case cons(v0, vs00):
                    if (k == 1) {
                    } else {
                        is_sorted_nth_neq_eq(vs0, k - 1, x);
                    }
            }
    }
}

lemma void is_sorted_nth_lt(list<int> vs, int k, int x)
    requires is_sorted_between(INT_MIN, vs, INT_MAX) == true &*& 0 <= k &*& k < length(vs) &*& nth(k, vs) < x;
    ensures is_sorted_between(INT_MIN - 1, take(k + 1, vs), x - 1) == true;
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
            if (k == 0) {
            } else {
                is_sorted_weaken(INT_MIN, v, vs0, INT_MAX, INT_MAX);
                is_sorted_nth_lt(vs0, k - 1, x);
                switch (vs0) { case nil: case cons(v0, vs00): }
            }
    }
}

lemma void is_sorted_nth_gt(list<int> vs, int k, int x)
    requires is_sorted_between(INT_MIN, vs, INT_MAX) == true &*& 0 <= k &*& k < length(vs) &*& nth(k, vs) > x;
    ensures is_sorted_between(x + 1, drop(k, vs), INT_MAX + 1) == true;
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
            if (k == 0) {
                is_sorted_weaken(INT_MIN, INT_MIN, vs, INT_MAX, INT_MAX + 1);
            } else {
                is_sorted_weaken(INT_MIN, v, vs0, INT_MAX, INT_MAX);
                is_sorted_nth_gt(vs0, k - 1, x);
            }
    }
}

lemma void is_sorted_p1_index_of(list<int> vs, int x)
    requires is_sorted_between(x + 1, vs, INT_MAX + 1) == true;
    ensures index_of(x, vs) == length(vs);
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
            is_sorted_weaken(x + 1, v, vs0, INT_MAX + 1, INT_MAX + 1);
            is_sorted_p1_index_of(vs0, x);
    }
}

lemma void is_sorted_m1_p1_index_of(list<int> vs, int k, int x)
    requires 0 <= k &*& k <= length(vs) &*& is_sorted_between(INT_MIN - 1, take(k, vs), x - 1) == true &*& is_sorted_between(x + 1, drop(k, vs), INT_MAX + 1) == true;
    ensures index_of(x, vs) == length(vs);
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
            if (k == 0) {
                is_sorted_p1_index_of(vs, x);
            } else {
                is_sorted_weaken(INT_MIN - 1, v, take(k - 1, vs0), x - 1, x - 1);
                is_sorted_m1_p1_index_of(vs0, k - 1, x);
                is_sorted_limits(INT_MIN - 1, v, take(k - 1, vs0), x - 1);
            }
    }
}

@*/

int binary_search(int *xs, int n, int x)
    //@ requires xs[0..n] |-> ?vs &*& is_sorted_between(INT_MIN, vs, INT_MAX) == true;
    //@ ensures xs[0..n] |-> vs &*& result == index_of(x, vs); // Returns n if not found.
{
    int l = 0;
    int r = n;
    while (l < r)
        /*@
        invariant
            xs[0..n] |-> vs &*& 0 <= l &*& l <= r &*& r <= n &*&
            is_sorted_between(INT_MIN - 1, take(l, vs), x - 1) == true &*&
            is_sorted_between(x + 1, drop(r, vs), INT_MAX + 1) == true;
        @*/
    {
        //@ div_rem(r - l, 2);
        int k = l + (r - l) / 2;
        int x0 = xs[k];
        if (x0 == x) {
            while (l < k && xs[k - 1] == x)
                //@ invariant xs[0..n] |-> vs &*& l <= k &*& k < r &*& nth(k, vs) == x;
            {
                k--;
            }
            /*@
            if (l < k) {
                is_sorted_nth_neq_eq(vs, k, x);
            }
            @*/
            //@ is_sorted_between_index_of(vs, x, k);
            return k;
        } else if (x0 < x) {
            l = k + 1;
            //@ is_sorted_nth_lt(vs, k, x);
        } else {
            r = k;
            //@ is_sorted_nth_gt(vs, k, x);
        }
    }
    //@ is_sorted_m1_p1_index_of(vs, l, x);
    return n;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    int n;
    int *xs;
    
    puts("How many numbers do you want to search?");
    n = read_int();
    if (n < 0 || 15000 <= n) abort();
    //@ case_split_sizeof_int();
    xs = malloc(n * sizeof(int));
    if (xs == 0) abort();
    for (int i = 0; ; i++)
        //@ requires xs[i..n] |-> _ &*& i <= n;
        //@ ensures xs[old_i..n] |-> ?vs;
    {
        //@ open ints_(_, _, _);
        if (i >= n)
          break;
        int x = read_int();
        xs[i] = x;
    }
    
    //@ ints_limits(xs);
    //@ assert xs[0..n] |-> ?vs0;
    merge_sort(xs, n);
    //@ sorted_is_sorted(vs0);
    
    for (;;)
        //@ invariant xs[0..n] |-> sorted(vs0);
    {
        puts("Enter a number to search for, or -1 to quit.");
        int x = read_int();
        if (x == -1) break;
        int i = binary_search(xs, n, x);
        if (i == n) {
            puts("The number does not appear in the list.");
        } else {
            printf("%i", i);
            puts("");
        }
    }
    free(xs);
    return 0;
}