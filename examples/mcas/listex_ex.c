//@ #include "listex_ex.gh"

/*@

lemma void drop_k_plus_one_alt<t>(int k, list<t> xs)
    requires 0 <= k &*& k <= length(xs) &*& drop(k, xs) != nil;
    ensures drop(k, xs) == cons(nth(k, xs), drop(k + 1, xs)) &*& length(xs) > k;
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        if (k == 0) {
        } else {
            drop_k_plus_one_alt(k - 1, xs0);
        }
    }
}

lemma void foreach_take_plus_one_unseparate<a>(int n, list<a> xs)
    requires 0 <= n &*& n < length(xs) &*& foreach(take(n, xs), ?p) &*& p(nth(n, xs));
    ensures foreach(take(n + 1, xs), p);
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        open foreach(take(n, xs), p);
        if (n == 0) {
            close foreach(nil, p);
        } else {
            foreach_take_plus_one_unseparate(n - 1, xs0);
        }
        close foreach(take(n + 1, xs), p);
    }
}

lemma void foreach_separate<t>(list<t> xs, t x)
    requires foreach(xs, ?p) &*& mem(x, xs) == true;
    ensures foreach(before(x, xs), p) &*& p(x) &*& foreach(after(x, xs), p);
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        open foreach(xs, p);
        if (x0 == x) {
            close foreach(nil, p);
        } else {
            foreach_separate(xs0, x);
            close foreach(before(x, xs), p);
        }
    }
}

lemma void foreach_unseparate<t>(list<t> xs, t x)
    requires mem(x, xs) == true &*& foreach(before(x, xs), ?p) &*& p(x) &*& foreach(after(x, xs), p);
    ensures foreach(xs, p);
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        open foreach(before(x, xs), p);
        if (x0 == x) {
        } else {
            foreach_unseparate(xs0, x);
        }
        close foreach(xs, p);
    }
}

lemma void foreach_separate_ith<t>(int i, list<t> es)
    requires foreach(es, ?p) &*& 0 <= i &*& i < length(es);
    ensures foreach(take(i, es), p) &*& p(nth(i, es)) &*& foreach(drop(i + 1, es), p);
{
    switch (es) {
    case nil:
    case cons(e0, es0):
        open foreach(es, p);
        if (i == 0) {
        } else {
            foreach_separate_ith(i - 1, es0);
        }
    }
    close foreach(take(i, es), p);
}

lemma void foreach_unseparate_ith_nochange<t>(int i, list<t> es)
    requires foreach(take(i, es), ?p) &*& p(nth(i, es)) &*& foreach(drop(i + 1, es), p) &*& 0 <= i &*& i < length(es);
    ensures foreach(es, p);
{
    switch (es) {
    case nil:
    case cons(e0, es0):
        open foreach(take(i, es), p);
        if (i == 0) {
        } else {
            foreach_unseparate_ith_nochange(i - 1, es0);
        }
        close foreach(es, p);
    }
}

@*/