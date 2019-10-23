//@ #include "strong_ghost_lists.gh"
//@ #include "ghost_cells.gh"
//@ #include "raw_ghost_lists.gh"
//@ #include "listex.gh"

/*@

fixpoint int count_eq<t>(t x, list<t> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(h, t): return (h == x ? 1 : 0) + count_eq(x, t);
    }
}

lemma void count_eq_append<t>(t x, list<t> xs, list<t> ys)
    requires true;
    ensures count_eq(x, append(xs, ys)) == count_eq(x, xs) + count_eq(x, ys);
{
    switch (xs) {
        case nil:
        case cons(h, t):
            count_eq_append(x, t, ys);
    }
}

fixpoint bool count_le<t>(unit u, list<t> xs, list<t> ys, t x) {
    switch (u) {
        case unit: return count_eq(x, xs) <= count_eq(x, ys);
    }
}

predicate strong_ghost_list<t>(int id; list<t> xs) =
    [_]ghost_cell(id, pair(?rawId, ?xsId)) &*& ghost_cell(xsId, xs) &*& raw_ghost_list<t>(rawId, _, ?es) &*& forall(map(snd, es), (count_le)(unit, map(snd, es), xs)) == true;

predicate strong_ghost_list_member_handle<t>(int id, t x) =
    [_]ghost_cell<pair<int, int> >(id, pair(?rawId, ?xsId)) &*& raw_ghost_list_member_handle<t>(rawId, _, x);

lemma int create_strong_ghost_list<t>()
    requires true;
    ensures strong_ghost_list<t>(result, nil);
{
    int rawId = create_raw_ghost_list();
    int xsId = create_ghost_cell(nil);
    int id = create_ghost_cell(pair(rawId, xsId));
    leak ghost_cell(id, _);
    close strong_ghost_list(id, nil);
    return id;
}

lemma void count_eq_nonnegative<t>(t x, list<t> xs)
    requires true;
    ensures 0 <= count_eq(x, xs);
{
    switch (xs) {
        case nil:
        case cons(h, t):
            count_eq_nonnegative(x, t);
    }
}

lemma void count_eq_mem<t>(t x, list<t> xs)
    requires true;
    ensures mem(x, xs) == (count_eq(x, xs) > 0);
{
    switch (xs) {
        case nil:
        case cons(h, t):
            count_eq_nonnegative(x, t);
            count_eq_mem(x, t);
    }
}

lemma void strong_ghost_list_member_handle_lemma<t>()
    requires [?fl]strong_ghost_list<t>(?id, ?xs) &*& [?fh]strong_ghost_list_member_handle<t>(id, ?x);
    ensures [fl]strong_ghost_list<t>(id, xs) &*& [fh]strong_ghost_list_member_handle<t>(id, x) &*& mem(x, xs) == true;
{
    open strong_ghost_list(id, xs);
    open strong_ghost_list_member_handle(id, x);
    assert [_]ghost_cell(id, pair(?rawId, ?xsId));
    assert [fl]raw_ghost_list(rawId, _, ?es);
    assert [fh]raw_ghost_list_member_handle(rawId, ?k, x);
    raw_ghost_list_match(rawId, k);
    mem_map(pair(k, x), es, snd);
    forall_mem(x, map(snd, es), (count_le)(unit, map(snd, es), xs));
    assert count_eq(x, map(snd, es)) <= count_eq(x, xs);
    assert mem(x, map(snd, es)) == true;
    count_eq_mem(x, map(snd, es));
    assert 0 < count_eq(x, map(snd, es));
    assert 0 < count_eq(x, xs);
    count_eq_mem(x, xs);
    assert mem(x, xs) == true;
    close [fl]strong_ghost_list<t>(id, xs);
    close [fh]strong_ghost_list_member_handle<t>(id, x);
}

lemma void forall_count_le<t>(list<pair<int, t> > es, list<pair<int, t> > es0, list<t> xs0, t x, list<t> xs1)
    requires forall(map(snd, es), (count_le)(unit, map(snd, es0), append(xs0, xs1))) == true;
    ensures forall(map(snd, es), (count_le)(unit, append(map(snd, es0), cons(x, nil)), append(xs0, cons(x, xs1)))) == true;
{
    switch (es) {
        case nil:
        case cons(e, es1):
            forall_count_le(es1, es0, xs0, x, xs1);
            count_eq_append(snd(e), map(snd, es0), cons(x, nil));
            count_eq_append(snd(e), xs0, xs1);
            count_eq_append(snd(e), xs0, cons(x, xs1));
            assert count_eq(snd(e), append(map(snd, es0), cons(x, nil))) <= count_eq(snd(e), append(xs0, cons(x, xs1)));
    }
}

lemma void strong_ghost_list_insert<t>(int id, list<t> xs0, list<t> xs1, t x)
    requires strong_ghost_list<t>(id, append(xs0, xs1));
    ensures strong_ghost_list<t>(id, append(xs0, cons(x, xs1))) &*& strong_ghost_list_member_handle<t>(id, x);
{
    open strong_ghost_list<t>(id, _);
    assert [_]ghost_cell(id, pair(?rawId, ?xsId));
    list<t> xs = append(xs0, xs1);
    list<t> xs2 = append(xs0, cons(x, xs1));
    assert raw_ghost_list(rawId, ?n, ?es);
    raw_ghost_list_add(rawId, x);
    assert raw_ghost_list(rawId, n + 1, ?es1);
    forall_append(map(snd, es), cons(x, nil), (count_le)(unit, map(snd, es1), xs2));
    map_append(snd, es, cons(pair(n, x), nil));
    assert map(snd, es1) == append(map(snd, es), cons(x, nil));
    forall_count_le(es, es, xs0, x, xs1);
    if (mem(x, map(snd, es))) {
        forall_mem(x, map(snd, es), (count_le)(unit, map(snd, es), xs));
        count_eq_append(x, xs0, xs1);
        count_eq_append(x, xs0, cons(x, xs1));
        count_eq_append(x, map(snd, es), cons(x, nil));
    } else {
        count_eq_mem(x, map(snd, es));
        count_eq_nonnegative(x, map(snd, es));
        assert count_eq(x, map(snd, es)) == 0;
        count_eq_append(x, map(snd, es), cons(x, nil));
        count_eq_append(x, xs0, xs1);
        count_eq_append(x, xs0, cons(x, xs1));
        assert count_eq(x, map(snd, es1)) == 1;
        assert count_eq(x, xs2) == count_eq(x, xs0) + count_eq(x, xs1) + 1;
        count_eq_nonnegative(x, xs0);
        count_eq_nonnegative(x, xs1);
        assert count_eq(x, map(snd, es1)) <= count_eq(x, xs2);
    }
    ghost_cell_mutate(xsId, append(xs0, cons(x, xs1)));
    close strong_ghost_list<t>(id, append(xs0, cons(x, xs1)));
    close strong_ghost_list_member_handle<t>(id, x);
}

predicate before_after<t>(list<t> xs, list<t> ys) = emp;

lemma void remove_elim<t>(t x, list<t> xs)
    requires mem(x, xs) == true;
    ensures
        before_after<t>(?xs0, ?xs1) &*&
        xs == append(xs0, cons(x, xs1)) &*&
        remove(x, xs) == append(xs0, xs1);
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (h == x) {
                close before_after<t>(nil, t);
            } else {
                remove_elim(x, t);
                open before_after<t>(?xs0, ?xs1);
                close before_after<t>(cons(h, xs0), xs1);
            }
    }
}

lemma void remove_iter<t>(list<pair<int, t> > esi, list<pair<int, t> > es0, int k, t x, list<pair<int, t> > es1, list<t> xs0, list<t> xs1)
    requires forall(map(snd, esi), (count_le)(unit, map(snd, append(es0, cons(pair(k, x), es1))), append(xs0, cons(x, xs1)))) == true;
    ensures forall(map(snd, esi), (count_le)(unit, map(snd, append(es0, es1)), append(xs0, xs1))) == true;
{
    switch (esi) {
        case nil:
        case cons(e, esi0):
            remove_iter(esi0, es0, k, x, es1, xs0, xs1);
            map_append(snd, es0, cons(pair(k, x), es1));
            map_append(snd, es0, es1);
            count_eq_append(snd(e), map(snd, es0), cons(x, map(snd, es1)));
            count_eq_append(snd(e), map(snd, es0), map(snd, es1));
            count_eq_append(snd(e), xs0, cons(x, xs1));
            count_eq_append(snd(e), xs0, xs1);
    }
}

lemma void strong_ghost_list_remove<t>(int id, list<t> xs0, list<t> xs1, t x)
    requires strong_ghost_list<t>(id, append(xs0, cons(x, xs1))) &*& strong_ghost_list_member_handle<t>(id, x);
    ensures strong_ghost_list<t>(id, append(xs0, xs1));
{
    open strong_ghost_list<t>(id, append(xs0, cons(x, xs1)));
    assert [_]ghost_cell(id, pair(?rawId, ?xsId));
    assert raw_ghost_list(rawId, ?n, ?es);
    open strong_ghost_list_member_handle<t>(id, x);
    assert raw_ghost_list_member_handle(rawId, ?k, x);
    raw_ghost_list_match(rawId, k);
    raw_ghost_list_remove(rawId, k);
    remove_elim(pair(k, x), es);
    open before_after(?es0, ?es1);
    list<pair<int, t> > esn = append(es0, es1);
    list<t> xsn = append(xs0, xs1);
    map_append(snd, es0, cons(pair(k, x), es1));
    map_append(snd, es0, es1);
    list<t> xs = append(xs0, cons(x, xs1));
    forall_append(map(snd, es0), cons(x, map(snd, es1)), (count_le)(unit, map(snd, es), xs));
    remove_iter(es0, es0, k, x, es1, xs0, xs1);
    remove_iter(es1, es0, k, x, es1, xs0, xs1);
    forall_append(map(snd, es0), map(snd, es1), (count_le)(unit, map(snd, esn), xsn));
    ghost_cell_mutate(xsId, append(xs0, xs1));
    close strong_ghost_list<t>(id, append(xs0, xs1));
}

@*/
