/*@

lemma void length_nonnegative<t>(list<t> xs)
    requires true;
    ensures length(xs) >= 0;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            length_nonnegative(xs0);
    }
}

lemma void append_nil<t>(list<t> xs)
    requires true;
    ensures append(xs, nil) == xs;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            append_nil(xs0);
    }
}

lemma void append_assoc<t>(list<t> xs, list<t> ys, list<t> zs)
    requires true;
    ensures append(append(xs, ys), zs) == append(xs, append(ys, zs));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            append_assoc(xs0, ys, zs);
    }
}

lemma void length_append<t>(list<t> xs, list<t> ys)
    requires true;
    ensures length(append(xs, ys)) == length(xs) + length(ys);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            length_append(xs0, ys);
    }
}

lemma void reverse_append<t>(list<t> xs, list<t> ys)
    requires true;
    ensures reverse(append(xs, ys)) == append(reverse(ys), reverse(xs));
{
    switch (xs) {
        case nil:
            append_nil(reverse(ys));
        case cons(x, xs0):
            assert reverse(append(xs, ys)) == reverse(append(cons(x, xs0), ys));
            assert reverse(append(cons(x, xs0), ys)) == reverse(cons(x, append(xs0, ys)));
            assert reverse(cons(x, append(xs0, ys))) == append(reverse(append(xs0, ys)), cons(x, nil));
            reverse_append(xs0, ys);
            assert append(reverse(append(xs0, ys)), cons(x, nil)) == append(append(reverse(ys), reverse(xs0)), cons(x, nil));
            append_assoc(reverse(ys), reverse(xs0), cons(x, nil));
            assert append(append(reverse(ys), reverse(xs0)), cons(x, nil)) == append(reverse(ys), append(reverse(xs0), cons(x, nil)));
            assert append(reverse(ys), append(reverse(xs0), cons(x, nil))) == append(reverse(ys), reverse(xs));
    }
}

lemma void reverse_reverse<t>(list<t> xs)
    requires true;
    ensures reverse(reverse(xs)) == xs;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            assert reverse(reverse(xs)) == reverse(reverse(cons(x, xs0)));
            assert reverse(reverse(cons(x, xs0))) == reverse(append(reverse(xs0), cons(x, nil)));
            reverse_append(reverse(xs0), cons(x, nil));
            assert reverse(append(reverse(xs0), cons(x, nil))) == append(cons(x, nil), reverse(reverse(xs0)));
            reverse_reverse(xs0);
    }
}

lemma void mem_nth<t>(int n, list<t> xs)
    requires 0 <= n && n < length(xs);
    ensures mem(nth(n, xs), xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                mem_nth(n - 1, xs0);
            }
    }
}

lemma void nth_zero<t>(list<t> vs)
    requires true;
    ensures nth(0, vs) == head(vs);
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
    }
}

lemma void take_0<t>(list<t> xs)
    requires true;
    ensures take(0, xs) == nil;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
    }
}

lemma void take_length<t>(list<t> xs)
    requires true;
    ensures take(length(xs), xs) == xs;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            length_nonnegative(xs0);
            take_length(xs0);
    }
}

lemma void length_take<t>(int n, list<t> xs)
    requires 0 <= n && n <= length(xs);
    ensures length(take(n, xs)) == n;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                length_take(n - 1, xs0);
            }
    }
}

lemma void length_take_n<t>(int n, list<t> xs)
    requires 0 <= n && n < length(xs);
    ensures length(take(n, xs)) == n;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                length_take(n - 1, xs0);
            }
    }
}

lemma void nth_take<t>(int i, int n, list<t> xs)
    requires 0 <= i && i < n && n <= length(xs);
    ensures nth(i, take(n, xs)) == nth(i, xs);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (i == 0) {
            } else {
                nth_take(i - 1, n - 1, xs0);
            }
    }
}

lemma void drop_0<t>(list<t> xs)
    requires true;
    ensures drop(0, xs) == xs;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
    }
}

lemma void drop_n_plus_one<t>(int n, list<t> xs)
    requires 0 <= n &*& n < length(xs);
    ensures drop(n, xs) == cons(nth(n, xs), drop(n + 1, xs));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
                drop_0(xs0);
            } else {
                drop_n_plus_one(n - 1, xs0);
            }
    }
}

lemma void drop_length<t>(list<t> xs)
    requires true;
    ensures drop(length(xs), xs) == nil;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            length_nonnegative(xs0);
            drop_length(xs0);
    }
}

lemma void length_drop<t>(int n, list<t> xs)
    requires 0 <= n && n <= length(xs);
    ensures length(drop(n, xs)) == length(xs) - n;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                length_drop(n - 1, xs0);
            }
    }
}

lemma void drop_n_take_n<t>(int n, list<t> xs)
    requires true;
    ensures drop(n, take(n, xs)) == nil;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                drop_n_take_n(n - 1, xs0);
            }
    }
}

lemma void append_take_drop<t>(int n, list<t> xs)
    requires 0 <= n && n < length(xs);
    ensures append(take(n, xs), drop(n, xs)) == xs;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                append_take_drop(n - 1, xs0);
            }
    }
}

lemma void nth_drop<t>(list<t> vs, int i)
    requires 0 <= i && i < length(vs);
    ensures nth(i, vs) == head(drop(i, vs));
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
            if (i == 0) {
            } else {
                nth_drop(vs0, i - 1);
            }
    }
}

lemma void drop_take_remove_nth<t>(list<t> xs, int n)
    requires 0 <= n && n < length(xs);
    ensures append(take(n, xs), tail(drop(n, xs))) == remove_nth(n, xs);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                drop_take_remove_nth(xs0, n - 1);
            }
    }
}

lemma void mem_index_of<t>(t x, list<t> xs)
    requires mem(x, xs) == true;
    ensures mem(x, xs) == (0 <= index_of(x, xs)) &*& index_of(x, xs) <= length(xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x == x0) {
                length_nonnegative(xs);
            } else {
                mem_index_of(x, xs0);
            }
    }
}

lemma void foreach_remove<t>(t x, list<t> xs)
    requires foreach(xs, ?p) &*& mem(x, xs) == true;
    ensures foreach(remove(x, xs), p) &*& p(x);
{
    open foreach(xs, p);
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x == x0) {
            } else {
                foreach_remove(x, xs0);
                close foreach(remove(x, xs), p);
            }
    }
}

lemma void foreach_unremove<t>(t x, list<t> xs)
    requires foreach(remove(x, xs), ?p) &*& mem(x, xs) == true &*& p(x);
    ensures foreach(xs, p);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x == x0) {
                close foreach(xs, p);
            } else {
                open foreach(remove(x, xs), p);
                foreach_unremove(x, xs0);
                close foreach(xs, p);
            }
    }
}

lemma void foreach_append<t>(list<t> xs, list<t> ys)
    requires foreach(xs, ?p) &*& foreach(ys, p);
    ensures foreach(append(xs, ys), p);
{
    open foreach(xs, p);
    switch (xs) {
        case nil:
        case cons(x, xs0):
            foreach_append(xs0, ys);
            close foreach(append(xs, ys), p);
    }
}

lemma void all_eq_append<t>(list<t> xs1, list<t> xs2, t x0)
    requires true;
    ensures all_eq(append(xs1, xs2), x0) == (all_eq(xs1, x0) && all_eq(xs2, x0));
{
    switch (xs1) {
        case nil:
        case cons(x, xs10):
            all_eq_append(xs10, xs2, x0);
    }
}

lemma void drop_append<t>(list<t> xs1, list<t> xs2)
    requires true;
    ensures drop(length(xs1), append(xs1, xs2)) == xs2;
{
    switch (xs1) {
        case nil:
            drop_0(xs2);
        case cons(x, xs10):
            length_nonnegative(xs10);
            drop_append(xs10, xs2);
    }
}

@*/