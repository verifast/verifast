//@ #include "assoc_list.gh"

//@ #include <listex.gh>

/*@

lemma void length_map<a, b>(fixpoint(a, b) f, list<a> xs)
    requires true;
    ensures length(map(f, xs)) == length(xs);
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        length_map(f, xs0);
    }
}

lemma void length_mapfst<a, b>(list<pair<a, b> > xys)
    requires true;
    ensures length(mapfst(xys)) == length(xys);
{
    length_map(fst, xys);
}

lemma void lt_drop_take<a>(int k, int i, list<a> xs)
    requires 0 <= k &*& k < i &*& i <= length(xs);
    ensures drop(k, take(i, xs)) == cons(nth(k, xs), drop(k + 1, take(i, xs)));
{
    drop_n_plus_one(k, take(i, xs));
}

lemma void nth_map<a, b>(int n, fixpoint(a, b) f, list<a> xs)
    requires 0 <= n &*& n < length(xs);
    ensures nth(n, map(f, xs)) == f(nth(n, xs));
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        if (n != 0)
            nth_map(n - 1, f, xs0);
    }
}

lemma void lt_drop_take_map_assoc_mapfst<a, b, c>(int k, int i, list<pair<a, b> > rcs, list<pair<a, c> > es)
    requires 0 <= k &*& k < i &*& i <= length(es);
    ensures
        drop(k, take(i, map_assoc(rcs, mapfst(es)))) ==
        cons(pair(fst(nth(k, es)), assoc(fst(nth(k, es)), rcs)), drop(k + 1, take(i, map_assoc(rcs, mapfst(es)))));
{
    length_map(fst, es);
    length_map((map_assoc_func)(rcs), mapfst(es));
    lt_drop_take(k, i, map_assoc(rcs, mapfst(es)));
    assert drop(k, take(i, map_assoc(rcs, mapfst(es)))) == cons(nth(k, map_assoc(rcs, mapfst(es))), drop(k + 1, take(i, map_assoc(rcs, mapfst(es)))));
    nth_map(k, (map_assoc_func)(rcs), mapfst(es));
    nth_map(k, fst, es);
}

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

lemma void assoc_fst_ith_snd_ith<a, b>(list<pair<a, b> > xys, int i)
    requires distinct(mapfst(xys)) == true &*& 0 <= i &*& i < length(xys);
    ensures assoc(fst(nth(i, xys)), xys) == snd(nth(i, xys));
{
    switch (xys) {
    case nil:
    case cons(xy0, xys0):
        assert xy0 == pair(?x0, ?y0);
        if (i == 0) {
        } else {
            if (x0 == fst(nth(i - 1, xys0))) {
                mem_nth(i - 1, xys0);
                mem_map(nth(i - 1, xys0), xys0, fst);
                assert false;
            }
            assoc_fst_ith_snd_ith(xys0, i - 1);
        }
    }
}

lemma void mem_mem_assoc<a, b>(a x, list<pair<a, b> > xys)
    requires mem(x, map(fst, xys)) == true;
    ensures mem(assoc(x, xys), map(snd, xys)) == true;
{
    switch (xys) {
    case nil:
    case cons(xy0, xys0):
        assert xy0 == pair(?x0, ?y0);
        if (x0 == x) {
        } else {
            mem_mem_assoc(x, xys0);
        }
    }
}

lemma void map_fst_snd_zip<a, b>(list<a> xs, list<b> ys)
    requires length(xs) == length(ys);
    ensures map(fst, zip(xs, ys)) == xs &*& map(snd, zip(xs, ys)) == ys;
{
    switch (xs) {
    case nil:
        switch (ys) { case nil: case cons(y0, ys0): }
    case cons(x0, xs0):
        assert ys == cons(?y0, ?ys0);
        map_fst_snd_zip(xs0, ys0);
    }
}

lemma void distinct_assoc_yzs<a, b, c>(list<a> xs, list<b> ys, list<c> zs, a x)
    requires distinct(ys) == true &*& length(ys) == length(xs) &*& length(zs) == length(xs) &*& mem(x, xs) == true;
    ensures assoc(x, zip(xs, zs)) == assoc(assoc(x, zip(xs, ys)), zip(ys, zs));
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        assert ys == cons(?y0, ?ys0) &*& zs == cons(?z0, ?zs0);
        if (x0 == x) {
        } else {
            assert assoc(x, zip(xs, zs)) == assoc(x, zip(xs0, zs0));
            assert assoc(x, zip(xs, ys)) == assoc(x, zip(xs0, ys0));
            map_fst_snd_zip(xs0, ys0);
            mem_mem_assoc(x, zip(xs0, ys0));
            assert mem(assoc(x, zip(xs0, ys0)), ys0) == true;
            assert assoc(assoc(x, zip(xs, ys)), zip(ys, zs)) == assoc(assoc(x, zip(xs0, ys0)), zip(ys0, zs0));
            distinct_assoc_yzs(xs0, ys0, zs0, x);
        }
    }
}

lemma void index_of_assoc_fst_ith<a, b>(list<pair<a, b> > xys, int i)
    requires distinct(mapfst(xys)) == true &*& 0 <= i &*& i < length(xys);
    ensures index_of_assoc(fst(nth(i, xys)), xys) == i;
{
    switch (xys) {
    case nil:
    case cons(xy0, xys0):
        assert xy0 == pair(?x0, ?y0);
        if (i == 0) {
        } else {
            mem_nth(i - 1, xys0);
            mem_map(nth(i - 1, xys0), xys0, fst);
            index_of_assoc_fst_ith(xys0, i - 1);
        }
    }
}

lemma void foreach_assoc_zip_pointer_distinct(list<void *> xs, list<void *> ys)
    requires foreach_assoc(zip(xs, ys), pointer) &*& length(ys) == length(xs);
    ensures foreach_assoc(zip(xs, ys), pointer) &*& distinct(xs) == true;
{
    open foreach_assoc(zip(xs, ys), pointer);
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        assert ys == cons(?y0, ?ys0);
        if (mem_assoc(x0, zip(xs0, ys0))) {
            foreach_assoc_separate(zip(xs0, ys0), x0);
            pointer_distinct(x0, x0);
            assert false;
        }
        map_fst_snd_zip(xs0, ys0);
        foreach_assoc_zip_pointer_distinct(xs0, ys0);
    }
    close foreach_assoc(zip(xs, ys), pointer);
}

lemma void foreach_assoc2_mapfst()
    requires foreach_assoc2(?xys, ?xzs, ?p);
    ensures foreach_assoc2(xys, xzs, p) &*& mapfst(xys) == mapfst(xzs);
{
    open foreach_assoc2(xys, xzs, p);
    if (xys != nil)
        foreach_assoc2_mapfst();
    close foreach_assoc2(xys, xzs, p);
}

lemma void close_foreach_assoc2_cons(list<pair<void *, void *> > xys, list<pair<void *, void *> > xzs, predicate(void *, void *, void *) p)
    requires xys == cons(pair(?x0, ?y0), ?xys0) &*& xzs == cons(pair(x0, ?z0), ?xzs0) &*&
        p(x0, y0, z0) &*& foreach_assoc2(xys0, xzs0, p);
    ensures foreach_assoc2(xys, xzs, p);
{
    close foreach_assoc2(xys, xzs, p);
}

lemma void foreach_assoc2_separate(void *x)
    requires foreach_assoc2(?xys, ?xzs, ?p) &*& mem_assoc(x, xys) || mem_assoc(x, xzs);
    ensures
        foreach_assoc2(before_assoc(x, xys), before_assoc(x, xzs), p) &*&
        p(x, assoc(x, xys), assoc(x, xzs)) &*&
        foreach_assoc2(after_assoc(x, xys), after_assoc(x, xzs), p) &*&
        mem_assoc(x, xys) == true &*& mem_assoc(x, xzs) == true &*&
        mapfst(xys) == mapfst(xzs);
{
    open foreach_assoc2(xys, xzs, p);
    assert xys == cons(pair(?x0, ?y0), ?xys0) &*& xzs == cons(pair(x0, ?z0), ?xzs0);
    if (x0 == x) {
        foreach_assoc2_mapfst();
        close foreach_assoc2(before_assoc(x, xys), before_assoc(x, xzs), p);
    } else {
        foreach_assoc2_separate(x);
        close_foreach_assoc2_cons(before_assoc(x, xys), before_assoc(x, xzs), p);
    }
}

lemma void foreach_assoc2_unseparate_1changed(list<pair<void *, void *> > xys, list<pair<void *, void *> > xzs, void *x)
    requires
        foreach_assoc2(before_assoc(x, xys), before_assoc(x, xzs), ?p) &*&
        mapfst(xys) == mapfst(xzs) &*&
        mem_assoc(x, xys) == true &*&
        p(x, ?y, assoc(x, xzs)) &*&
        foreach_assoc2(after_assoc(x, xys), after_assoc(x, xzs), p);
    ensures foreach_assoc2(update_assoc(xys, x, y), xzs, p);
{
    open foreach_assoc2(before_assoc(x, xys), before_assoc(x, xzs), p);
    assert xys == cons(pair(?x0, ?y0), ?xys0) &*& xzs == cons(pair(x0, ?z0), ?xzs0);
    if (x0 == x) {
    } else {
        foreach_assoc2_unseparate_1changed(xys0, xzs0, x);
    }
    close foreach_assoc2(update_assoc(xys, x, y), xzs, p);
}

lemma void foreach_assoc2_unseparate_nochange(list<pair<void *, void *> > xys, list<pair<void *, void *> > xzs, void *x)
    requires
        foreach_assoc2(before_assoc(x, xys), before_assoc(x, xzs), ?p) &*&
        mapfst(xys) == mapfst(xzs) &*&
        mem_assoc(x, xys) == true &*&
        p(x, assoc(x, xys), assoc(x, xzs)) &*&
        foreach_assoc2(after_assoc(x, xys), after_assoc(x, xzs), p);
    ensures foreach_assoc2(xys, xzs, p);
{
    open foreach_assoc2(before_assoc(x, xys), before_assoc(x, xzs), p);
    assert xys == cons(pair(?x0, ?y0), ?xys0) &*& xzs == cons(pair(x0, ?z0), ?xzs0);
    if (x0 == x) {
    } else {
        foreach_assoc2_unseparate_nochange(xys0, xzs0, x);
    }
    close foreach_assoc2(xys, xzs, p);
}

lemma void close_foreach3_cons(list<void *> xs, list<void *> ys, list<void *> zs, predicate(void *, void *, void *) p)
    requires xs == cons(?x0, ?xs0) &*& ys == cons(?y0, ?ys0) &*& zs == cons(?z0, ?zs0) &*& p(x0, y0, z0) &*& foreach3(xs0, ys0, zs0, p);
    ensures foreach3(xs, ys, zs, p);
{
    close foreach3(xs, ys, zs, p);
}

lemma void foreach3_length()
    requires foreach3(?xs, ?ys, ?zs, ?p);
    ensures foreach3(xs, ys, zs, p) &*& length(ys) == length(xs) &*& length(zs) == length(xs);
{
    open foreach3(xs, ys, zs, p);
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        foreach3_length();
    }
    close foreach3(xs, ys, zs, p);
}

lemma void foreach3_mem_x_mem_assoc_x_ys(void *x)
    requires foreach3(?xs, ?ys, ?zs, ?p) &*& mem(x, xs) == true;
    ensures foreach3(xs, ys, zs, p) &*& mem(assoc(x, zip(xs, ys)), ys) == true;
{
    foreach3_length();
    map_fst_snd_zip(xs, ys);
    mem_mem_assoc(x, zip(xs, ys));
}

lemma void foreach3_separate(void *x)
    requires foreach3(?xs, ?ys, ?zs, ?p) &*& mem(x, xs) == true;
    ensures
        foreach3(before(x, xs), before2(x, xs, ys), before2(x, xs, zs), p) &*&
        p(x, assoc(x, zip(xs, ys)), assoc(x, zip(xs, zs))) &*&
        foreach3(after(x, xs), after2(x, xs, ys), after2(x, xs, zs), p) &*&
        length(ys) == length(xs) &*&
        length(zs) == length(xs);
{
    open foreach3(xs, ys, zs, p);
    assert xs == cons(?x0, ?xs0);
    assert ys == cons(?y0, ?ys0);
    assert zs == cons(?z0, ?zs0);
    if (x0 == x) {
        foreach3_length();
        close foreach3(nil, nil, nil, p);
    } else {
        foreach3_separate(x);
        foreach3_length();
        close_foreach3_cons(before(x, xs), before2(x, xs, ys), before2(x, xs, zs), p);
    }
}

lemma void foreach3_unseparate_nochange(list<void *> xs, list<void *> ys, list<void *> zs, void *x)
    requires
        foreach3(before(x, xs), before2(x, xs, ys), before2(x, xs, zs), ?p) &*&
        p(x, assoc(x, zip(xs, ys)), assoc(x, zip(xs, zs))) &*&
        foreach3(after(x, xs), after2(x, xs, ys), after2(x, xs, zs), p) &*&
        length(ys) == length(xs) &*&
        length(zs) == length(xs) &*&
        mem(x, xs) == true;
    ensures foreach3(xs, ys, zs, p);
{
    open foreach3(before(x, xs), before2(x, xs, ys), before2(x, xs, zs), p);
    assert xs == cons(?x0, ?xs0) &*& ys == cons(?y0, ?ys0) &*& zs == cons(?z0, ?zs0);
    if (x0 == x) {
    } else {
        foreach3_unseparate_nochange(xs0, ys0, zs0, x);
    }
    close foreach3(xs, ys, zs, p);
}

lemma void foreach3_foreach_assoc_separate(void *x)
    requires foreach3(?xs, ?ys, ?zs, ?p) &*& foreach_assoc(zip(ys, zs), ?q) &*& mem(x, xs) == true;
    ensures
        foreach3(before(x, xs), before2(x, xs, ys), before2(x, xs, zs), p) &*& foreach_assoc(zip(before2(x, xs, ys), before2(x, xs, zs)), q) &*&
        p(x, assoc(x, zip(xs, ys)), assoc(x, zip(xs, zs))) &*& q(assoc(x, zip(xs, ys)), assoc(x, zip(xs, zs))) &*&
        foreach3(after(x, xs), after2(x, xs, ys), after2(x, xs, zs), p) &*& foreach_assoc(zip(after2(x, xs, ys), after2(x, xs, zs)), q);
{
    open foreach3(xs, ys, zs, p);
    open foreach_assoc(zip(ys, zs), q);
    assert xs == cons(?x0, ?xs0) &*& ys == cons(?y0, ?ys0) &*& zs == cons(?z0, ?zs0);
    if (x0 == x) {
        close foreach3(before(x, xs), before2(x, xs, ys), before2(x, xs, zs), p);
    } else {
        foreach3_foreach_assoc_separate(x);
        close_foreach3_cons(before(x, xs), before2(x, xs, ys), before2(x, xs, zs), p);
    }
    close foreach_assoc(zip(before2(x, xs, ys), before2(x, xs, zs)), q);
}

lemma void foreach3_foreach_assoc_unseparate(list<void *> xs, list<void *> ys, list<void *> zs, void *x)
    requires
        foreach3(before(x, xs), before2(x, xs, ys), before2(x, xs, zs), ?p) &*& foreach_assoc(zip(before2(x, xs, ys), before2(x, xs, zs)), ?q) &*&
        p(x, assoc(x, zip(xs, ys)), ?z) &*& q(assoc(x, zip(xs, ys)), z) &*&
        foreach3(after(x, xs), after2(x, xs, ys), after2(x, xs, zs), p) &*& foreach_assoc(zip(after2(x, xs, ys), after2(x, xs, zs)), q) &*&
        mem(x, xs) == true;
    ensures foreach3(xs, ys, update2(xs, zs, x, z), p) &*& foreach_assoc(zip(ys, update2(xs, zs, x, z)), q);
{
    open foreach3(before(x, xs), before2(x, xs, ys), before2(x, xs, zs), p);
    open foreach_assoc(zip(before2(x, xs, ys), before2(x, xs, zs)), q);
    assert xs == cons(?x0, ?xs0);
    assert ys == cons(?y0, ?ys0);
    assert zs == cons(?z0, ?zs0);
    if (x0 == x) {
    } else {
        foreach3_foreach_assoc_unseparate(xs0, ys0, zs0, x);
    }
    close foreach3(xs, ys, update2(xs, zs, x, z), p);
    close foreach_assoc(zip(ys, update2(xs, zs, x, z)), q);
}

lemma void foreach3_foreach_assoc_unseparate_nochange(list<void *> xs, list<void *> ys, list<void *> zs, void *x)
    requires
        foreach3(before(x, xs), before2(x, xs, ys), before2(x, xs, zs), ?p) &*& foreach_assoc(zip(before2(x, xs, ys), before2(x, xs, zs)), ?q) &*&
        p(x, assoc(x, zip(xs, ys)), assoc(x, zip(xs, zs))) &*& q(assoc(x, zip(xs, ys)), assoc(x, zip(xs, zs))) &*&
        foreach3(after(x, xs), after2(x, xs, ys), after2(x, xs, zs), p) &*& foreach_assoc(zip(after2(x, xs, ys), after2(x, xs, zs)), q) &*&
        mem(x, xs) == true;
    ensures foreach3(xs, ys, zs, p) &*& foreach_assoc(zip(ys, zs), q);
{
    open foreach3(before(x, xs), before2(x, xs, ys), before2(x, xs, zs), p);
    open foreach_assoc(zip(before2(x, xs, ys), before2(x, xs, zs)), q);
    assert xs == cons(?x0, ?xs0);
    assert ys == cons(?y0, ?ys0);
    assert zs == cons(?z0, ?zs0);
    if (x0 == x) {
    } else {
        foreach3_foreach_assoc_unseparate_nochange(xs0, ys0, zs0, x);
    }
    close foreach3(xs, ys, zs, p);
    close foreach_assoc(zip(ys, zs), q);
}



@*/