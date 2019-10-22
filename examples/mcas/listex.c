//@ #include "listex.gh"

/*@

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

@*/