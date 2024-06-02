// VSTTE 2010 Competition Problem 2. Problem statement by P. Mueller and N. Shankar.

//@ #include "nat.gh"
//@ #include "listex.gh"

/*@

fixpoint bool between(unit u, int lower, int upper, int x) {
    switch (u) {
        case unit: return lower <= x && x <= upper;
    }
}

fixpoint list<pair<int, t> > with_index<t>(int i, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return cons(pair(i, x), with_index(i + 1, xs0));
    }
}

lemma void with_index_append<t>(int i, list<t> xs, list<t> ys)
    requires true;
    ensures with_index(i, append(xs, ys)) == append(with_index(i, xs), with_index(i + length(xs), ys));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            with_index_append(i + 1, xs0, ys);
    }
}

fixpoint bool is_inverse(list<int> bs, pair<int, int> ia) {
    switch (ia) {
        case pair(i, a): return nth(a, bs) == i;
    }
}

lemma void ints_split(int *array, int offset)
    requires ints(array, ?N, ?as) &*& 0 <= offset &*& offset <= N;
    ensures ints(array, offset, take(offset, as)) &*& ints(array + offset, N - offset, drop(offset, as));
{
    if (offset == 0) {
        close ints(array, 0, nil);
    } else {
        open ints(array, N, as);
        ints_split(array + 1, offset - 1);
        close ints(array, offset, take(offset, as));
    }
}

lemma void ints_unseparate_same(int *array, list<int> xs)
    requires ints(array, ?M, take(M, xs)) &*& integer(array + M, head(drop(M, xs))) &*& ints(array + M + 1, ?N, tail(drop(M, xs))) &*& length(xs) == M + N + 1;
    ensures ints(array, M + N + 1, xs) &*& head(drop(M, xs)) == nth(M, xs);
{
    open ints(array, M, _);
    switch (drop(M, xs)) { default: }
    if (M != 0) {
        switch (xs) {
            case nil:
            case cons(h, t):
                ints_unseparate_same(array + 1, t);
                close ints(array, M + N + 1, _);
        }
    }
}

lemma void ints_merge(int *array)
    requires ints(array, ?M, ?as) &*& ints(array + M, ?N, ?bs);
    ensures ints(array, M + N, append(as, bs));
{
    open ints(array, M, _);
    if (M != 0) {
        ints_merge(array + 1);
        close ints(array, M + N, append(as, bs));
    }
}

lemma void ints_unseparate(int *array, int i, list<int> xs)
    requires ints(array, i, take(i, xs)) &*& integer(array + i, ?y) &*& ints(array + i + 1, length(xs) - i - 1, tail(drop(i, xs)));
    ensures ints(array, length(xs), update(i, y, xs));
{
    open ints(array, _, _);
    if (i == 0) {
        switch (xs) { default: }
    } else {
        switch (xs) { default: }
        ints_unseparate(array + 1, i - 1, tail(xs));
    }
    close ints(array, length(xs), update(i, y, xs));
}

lemma void forall_with_index_take_is_inverse(list<int> as, int i, list<int> bs, int ai, int k)
    requires
        forall(with_index(k, take(i - k, as)), (is_inverse)(bs)) == true &*&
        0 <= i &*& i - k < length(as) &*& 0 <= ai &*& ai < length(bs) &*&
        forall(as, (between)(unit, 0, length(bs) - 1)) == true &*& 0 <= k &*& k <= i &*&
        !mem(ai, take(i - k, as));
    ensures forall(with_index(k, take(i - k, as)), (is_inverse)(update(ai, i, bs))) == true;
{
    switch (as) {
        case nil:
        case cons(a, as0):
            if (k != i)
                forall_with_index_take_is_inverse(as0, i, bs, ai, k + 1);
            nth_update(a, ai, i, bs);
    }
}

lemma void forall_between_remove_max(int n, int x, list<int> xs)
    requires forall(cons(x, xs), (between)(unit, 0, n)) == true &*& distinct(cons(x, xs)) == true;
    ensures 0 <= max(x, xs) &*& max(x, xs) <= n &*& forall(remove(max(x, xs), cons(x, xs)), (between)(unit, 0, max(x, xs) - 1)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x < x0) {
                forall_between_remove_max(n, x0, xs0);
            } else {
                forall_between_remove_max(n, x, xs0);
            }
    }
}

lemma void forall_between_weaken(int a, int b1, int b2, list<int> xs)
    requires forall(xs, (between)(unit, a, b1)) == true &*& b1 <= b2;
    ensures forall(xs, (between)(unit, a, b2)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            forall_between_weaken(a, b1, b2, xs0);
    }
}

lemma void forall_between_distinct(nat n, list<int> xs)
    requires forall(xs, (between)(unit, 0, int_of_nat(n) - 1)) == true &*& distinct(xs) == true;
    ensures length(xs) <= int_of_nat(n);
{
    switch (n) {
        case zero:
            switch (xs) {
                case nil:
                case cons(x0, xs0):
            }
        case succ(n0):
            switch (xs) {
                case nil:
                case cons(x0, xs0):
                    forall_between_remove_max(int_of_nat(n) - 1, x0, xs0);
                    forall_between_weaken(0, max(x0, xs0) - 1, int_of_nat(n) - 2, remove(max(x0, xs0), cons(x0, xs0)));
                    distinct_remove(max(x0, xs0), cons(x0, xs0));
                    forall_between_distinct(n0, remove(max(x0, xs0), xs));
                    mem_max(x0, xs0);
                    length_remove(max(x0, xs0), cons(x0, xs0));
            }
    }
}

lemma void lt_le_conflict(int x, int y) // Needed for Redux, not for Z3
    requires x < y &*& y <= x;
    ensures false;
{
}

lemma void forall_between_distinct_mem(nat n, list<int> xs, int i)
    requires
        forall(xs, (between)(unit, 0, int_of_nat(n) - 1)) == true &*& distinct(xs) == true &*&
        length(xs) == int_of_nat(n) &*& 0 <= i &*& i < length(xs);
    ensures mem(i, xs) == true;
{
    switch (n) {
        case zero:
        case succ(n0):
            switch (xs) {
                case nil:
                case cons(x0, xs0):
                    forall_between_remove_max(int_of_nat(n) - 1, x0, xs0);
                    if (i == length(xs) - 1) {
                        if (max(x0, xs0) == i) {
                            mem_max(x0, xs0);
                        } else {
                            distinct_remove(max(x0, xs0), xs);
                            int_of_nat_of_int(max(x0, xs0));
                            forall_between_distinct(nat_of_int(max(x0, xs0)), remove(max(x0, xs0), xs));
                        }
                    } else {
                        forall_between_weaken(0, max(x0, xs0) - 1, int_of_nat(n0) - 1, remove(max(x0, xs0), xs));
                        distinct_remove(max(x0, xs0), xs);
                        mem_max(x0, xs0);
                        length_remove(max(x0, xs0), xs);
                        forall_between_distinct_mem(n0, remove(max(x0, xs0), xs), i);
                        mem_remove_mem(i, max(x0, xs0), xs);
                    }
            }
    }
}

lemma void nth_with_index<t>(int n, int i, list<t> xs)
    requires 0 <= n &*& n < length(xs);
    ensures nth(n, with_index(i, xs)) == pair(i + n, nth(n, xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n != 0)
                nth_with_index(n - 1, i + 1, xs0);
    }
}

lemma void length_with_index<t>(int k, list<t> xs)
    requires true;
    ensures length(with_index(k, xs)) == length(xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            length_with_index(k + 1, xs0);
    }
}

lemma void is_inverse_symm(list<int> as, nat n, list<int> bs, int i)
    requires
        forall(as, (between)(unit, 0, length(as) - 1)) == true &*& distinct(as) == true &*& length(bs) == length(as) &*&
        forall(with_index(0, as), (is_inverse)(bs)) == true &*&
        int_of_nat(n) <= length(bs) &*& i == length(bs) - int_of_nat(n);
    ensures
        forall(with_index(i, drop(i, bs)), (is_inverse)(as)) == true &*& distinct(drop(i, bs)) == true;
{
    switch (n) {
        case zero:
            drop_0(bs);
        case succ(n0):
            drop_n_plus_one(i, bs);
            is_inverse_symm(as, n0, bs, i + 1);
            int_of_nat_of_int(length(as));
            forall_between_distinct_mem(nat_of_int(length(as)), as, i);
            mem_nth_index_of(i, as);
            int k = index_of(i, as);
            nth_with_index(k, 0, as);
            length_with_index(0, as);
            mem_nth(k, with_index(0, as));
            forall_mem(pair(k, i), with_index(0, as), (is_inverse)(bs));
            if (mem(k, drop(i + 1, bs))) {
                int kk = index_of(k, drop(i + 1, bs));
                mem_nth_index_of(k, drop(i + 1, bs));
                nth_drop(kk, i + 1, bs);
                int kkk = i + 1 + kk;
                length_with_index(i + 1, drop(i + 1, bs));
                mem_nth(kk, with_index(i + 1, drop(i + 1, bs)));
                nth_with_index(kk, i + 1, drop(i + 1, bs));
                forall_mem(pair(kkk, k), with_index(i + 1, drop(i + 1, bs)), (is_inverse)(as));
            }
    }
}

@*/

void invert(int *A, int N, int *B)
    //@ requires ints(A, N, ?as) &*& ints(B, N, _) &*& forall(as, (between)(unit, 0, N - 1)) == true &*& distinct(as) == true;
    /*@
    ensures
        ints(A, N, as) &*& ints(B, N, ?bs) &*&
        forall(with_index(0, as), (is_inverse)(bs)) == true &*&
        forall(with_index(0, bs), (is_inverse)(as)) == true &*&
        distinct(bs) == true;
    @*/
{
    for (int i = 0; i < N; i++)
        /*@
        invariant ints(A, N, as) &*& ints(B, N, ?bs) &*& 0 <= i &*& i <= N &*& forall(with_index(0, take(i, as)), (is_inverse)(bs)) == true;
        @*/
    {
        //@ ints_split(A, i);
        //@ open ints(A + i, N - i, ?as1);
        int ai = *(A + i);
        //@ close ints(A + i, N - i, as1);
        //@ ints_unseparate_same(A, as);
        //@ forall_drop(as, (between)(unit, 0, N - 1), i);
        //@ ints_split(B, ai);
        *(B + ai) = i;
        //@ ints_unseparate(B, ai, bs);
        //@ take_plus_one(i, as);
        //@ with_index_append(0, take(i, as), cons(nth(i, as), nil));
        //@ forall_append(with_index(0, take(i, as)), with_index(i, cons(nth(i, as), nil)), (is_inverse)(update(ai, i, bs)));
        //@ assert ai == nth(i, as);
        //@ distinct_mem_nth_take(as, i);
        //@ assert !mem(ai, take(i, as));
        //@ forall_with_index_take_is_inverse(as, i, bs, ai, 0);
        //@ nth_update(ai, ai, i, bs);
    }
    //@ assert ints(B, N, ?bs);
    //@ int_of_nat_of_int(N);
    //@ is_inverse_symm(as, nat_of_int(N), bs, 0);
}
