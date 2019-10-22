//@ #include "assoc_list.gh"

/*@

lemma void mem_zip_mem_assoc_lemma(void *x, list<void *> xs, list<void *> ys)
    requires mem(x, xs) == true;
    ensures mem_assoc(x, zip(xs, ys)) == true;
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        switch (ys) { case nil: case cons(y0, ys0): }
        if (x0 == x) {
        } else {
            mem_zip_mem_assoc_lemma(x, xs0, tail(ys));
        }
    }
}

lemma void foreach_assoc_separate(list<pair<void *, void *> > xys, void **x)
    requires foreach_assoc(xys, ?p) &*& mem_assoc(x, xys) == true;
    ensures foreach_assoc(before_assoc(x, xys), p) &*& p(x, assoc(x, xys)) &*& foreach_assoc(after_assoc(x, xys), p);
{
    switch (xys) {
    case nil:
    case cons(xy0, xys0):
        assert xy0 == pair(?x0, ?y0);
        open foreach_assoc(xys, p);
        if (x0 == x) {
        } else {
            foreach_assoc_separate(xys0, x);
        }
        close foreach_assoc(before_assoc(x, xys), p);
    }
}

lemma void foreach_assoc_unseparate(list<pair<void *, void *> > xys, void **x)
    requires mem_assoc(x, xys) == true &*& foreach_assoc(before_assoc(x, xys), ?p) &*& p(x, ?y) &*& foreach_assoc(after_assoc(x, xys), p);
    ensures foreach_assoc(update_assoc(xys, x, y), p);
{
    switch (xys) {
    case nil:
    case cons(xy0, xys0):
        assert xy0 == pair(?x0, ?y0);
        open foreach_assoc(before_assoc(x, xys), p);
        if (x0 == x) {
        } else {
            foreach_assoc_unseparate(xys0, x);
        }
        close foreach_assoc(update_assoc(xys, x, y), p);
    }
}

lemma void foreach_assoc_unseparate_nochange(list<pair<void *, void *> > xys, void **x)
    requires mem_assoc(x, xys) == true &*& foreach_assoc(before_assoc(x, xys), ?p) &*& p(x, assoc(x, xys)) &*& foreach_assoc(after_assoc(x, xys), p);
    ensures foreach_assoc(xys, p);
{
    switch (xys) {
    case nil:
    case cons(xy0, xys0):
        assert xy0 == pair(?x0, ?y0);
        open foreach_assoc(before_assoc(x, xys), p);
        if (x0 == x) {
        } else {
            foreach_assoc_unseparate_nochange(xys0, x);
        }
        close foreach_assoc(xys, p);
    }
}

@*/