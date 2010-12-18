// VSTTE 2010 Competition Problem 2. Problem statement by P. Mueller and N. Shankar.

#include "nat.h"

/*@

predicate ints(int *array, int n; list<int> elems) =
    n == 0 ?
        elems == nil
    :
        integer(array, ?elem) &*& ints(array + 1, n - 1, ?elems0) &*& elems == cons(elem, elems0);

lemma_auto void ints_inv()
    requires ints(?array, ?n, ?elems);
    ensures ints(array, n, elems) &*& 0 <= n &*& length(elems) == n;
{
    open ints(array, n, elems);
    if (n != 0)
        ints_inv();
    close ints(array, n, elems);
}

lemma void forall_append<t>(list<t> xs, list<t> ys, fixpoint(t, bool) p)
    requires true;
    ensures forall(append(xs, ys), p) == (forall(xs, p) && forall(ys, p));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            forall_append(xs0, ys, p);
    }
}

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
    switch (drop(M, xs)) { case nil: case cons(x0, xs0): }
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

fixpoint list<t> update<t>(int i, t y, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return i == 0 ? cons(y, xs0) : cons(x, update(i - 1, y, xs0));
    }
}

lemma void ints_unseparate(int *array, int i, list<int> xs)
    requires ints(array, i, take(i, xs)) &*& integer(array + i, ?y) &*& ints(array + i + 1, length(xs) - i - 1, tail(drop(i, xs)));
    ensures ints(array, length(xs), update(i, y, xs));
{
    open ints(array, _, _);
    if (i == 0) {
        switch (xs) { case nil: case cons(x, xs0): }
    } else {
        switch (xs) { case nil: case cons(x, xs0): }
        ints_unseparate(array + 1, i - 1, tail(xs));
    }
    close ints(array, length(xs), update(i, y, xs));
}

lemma void forall_drop<t>(list<t> xs, fixpoint(t, bool) p, int i)
    requires forall(xs, p) == true;
    ensures forall(drop(i, xs), p) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            forall_drop(xs0, p, i - 1);
    }
}

lemma void take_plus_one<t>(int i, list<t> xs)
    requires 0 <= i &*& i < length(xs);
    ensures take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (i != 0) {
                take_plus_one(i - 1, xs0);
            }
    }
}

lemma void distinct_mem_nth_take<t>(list<t> xs, int i)
    requires distinct(xs) == true &*& 0 <= i &*& i < length(xs);
    ensures !mem(nth(i, xs), take(i, xs));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (i != 0) {
                distinct_mem_nth_take(xs0, i - 1);
            }
    }
}

lemma void nth_update<t>(int i, int j, t y, list<t> xs)
    requires 0 <= i &*& i < length(xs) &*& 0 <= j &*& j < length(xs);
    ensures nth(i, update(j, y, xs)) == (i == j ? y : nth(i, xs));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (i != 0 && j != 0)
                nth_update(i - 1, j - 1, y, xs0);
    }
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

lemma void mem_remove_diff<t>(t x, t y, list<t> xs)
    requires x != y;
    ensures mem(x, remove(y, xs)) == mem(x, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            mem_remove_diff(x, y, xs0);
    }
}

lemma void mem_mem_remove<t>(t x, t y, list<t> xs)
    requires mem(x, remove(y, xs)) == true;
    ensures mem(x, xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 != x && x0 != y)
                mem_mem_remove(x, y, xs0);
    }
}

lemma void distinct_mem_remove<t>(t x, list<t> xs)
    requires distinct(xs) == true;
    ensures !mem(x, remove(x, xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            distinct_mem_remove(x, xs0);
    }
}

lemma void distinct_remove<t>(t x, list<t> xs)
    requires distinct(xs) == true;
    ensures distinct(remove(x, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
            } else {
                distinct_remove(x, xs0);
                mem_remove_diff(x0, x, xs0);
            }
    }
}

fixpoint int max(int x, list<int> xs) {
    switch (xs) {
        case nil: return x;
        case cons(x0, xs0): return x < x0 ? max(x0, xs0) : max(x, xs0);
    }
}

lemma void mem_max(int x, list<int> xs)
    requires true;
    ensures mem(max(x, xs), cons(x, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x < x0) {
                mem_max(x0, xs0);
            } else {
                mem_max(x, xs0);
            }
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

lemma void length_remove(int x, list<int> xs)
    requires mem(x, xs) == true;
    ensures length(remove(x, xs)) == length(xs) - 1;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x != x0)
                length_remove(x, xs0);
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

lemma void mem_nth_index_of<t>(t x, list<t> xs)
    requires mem(x, xs) == true;
    ensures nth(index_of(x, xs), xs) == x;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 != x)
                mem_nth_index_of(x, xs0);
    }
}

lemma void lt_le_conflict(int x, int y)
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
                            mem_max(x0, xs0);
                            length_remove(max(x0, xs0), xs);
                            lt_le_conflict(max(x0, xs0), i); // For the Redux SMT solver. TODO: Fix this Redux bug.
                        }
                    } else {
                        forall_between_weaken(0, max(x0, xs0) - 1, int_of_nat(n0) - 1, remove(max(x0, xs0), xs));
                        distinct_remove(max(x0, xs0), xs);
                        mem_max(x0, xs0);
                        length_remove(max(x0, xs0), xs);
                        forall_between_distinct_mem(n0, remove(max(x0, xs0), xs), i);
                        mem_mem_remove(i, max(x0, xs0), xs);
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

lemma void mem_forall<t>(t x, list<t> xs, fixpoint(t, bool) p)
    requires forall(xs, p) == true &*& mem(x, xs) == true;
    ensures p(x) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 != x)
                mem_forall(x, xs0, p);
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

lemma void nth_drop<t>(int n, int k, list<t> xs)
    requires 0 <= n &*& 0 <= k &*& n + k < length(xs);
    ensures nth(n, drop(k, xs)) == nth(n + k, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (k != 0) {
                drop_n_plus_one(k, xs);
                nth_drop(n, k - 1, xs0);
            }
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
            mem_forall(pair(k, i), with_index(0, as), (is_inverse)(bs));
            if (mem(k, drop(i + 1, bs))) {
                int kk = index_of(k, drop(i + 1, bs));
                mem_nth_index_of(k, drop(i + 1, bs));
                nth_drop(kk, i + 1, bs);
                int kkk = i + 1 + kk;
                length_with_index(i + 1, drop(i + 1, bs));
                mem_nth(kk, with_index(i + 1, drop(i + 1, bs)));
                nth_with_index(kk, i + 1, drop(i + 1, bs));
                mem_forall(pair(kkk, k), with_index(i + 1, drop(i + 1, bs)), (is_inverse)(as));
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
