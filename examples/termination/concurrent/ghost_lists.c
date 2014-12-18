//@ #include "listex.gh"
//@ #include "ghost_cells.gh"
//@ #include "ghost_maps.gh"
//@ #include "ghost_counters.gh"
//@ #include "ghost_lists.gh"

/*@

lemma void mem_remove_eq_append<t>(t x, list<t> xs)
    requires mem(x, xs) == true;
    ensures exists<pair<list<t>, list<t> > >(pair(?xs1, ?xs2)) &*& xs == append(xs1, cons(x, xs2)) &*& remove(x, xs) == append(xs1, xs2);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                close exists(pair(nil, xs0));
            } else {
                mem_remove_eq_append(x, xs0);
                open exists(pair(?xs01, ?xs02));
                close exists(pair(cons(x0, xs01), xs02));
            }
    }
}

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

predicate counts_ok<t>(list<t> xs, list<pair<t, int> > ps;) =
    switch (ps) {
        case nil: return true;
        case cons(p, ps0): return
            p == pair(?x, ?counterId) &*& ghost_counter(counterId, ?n) &*& count_eq(x, xs) >= n &*&
            counts_ok(xs, ps0);
    };

predicate ghost_list<t>(int id; list<t> xs) =
    [_]ghost_cell<pair<int, int> >(id, pair(?mapId, ?listId)) &*&
    ghost_map<t, int>(mapId, ?entries) &*&
    ghost_cell<list<t> >(listId, xs) &*&
    counts_ok(xs, entries);

predicate ghost_list_member_handle<t>(int id, t x;) =
    [_]ghost_cell<pair<int, int> >(id, pair(?mapId, _)) &*&
    [_]ghost_map_entry_handle(mapId, x, ?counterId) &*&
    ghost_counter_ticket(counterId);

lemma int create_ghost_list<t>()
    requires true;
    ensures ghost_list<t>(result, nil);
{
    int mapId = create_ghost_map<t, int>();
    int listId = create_ghost_cell<list<t> >(nil);
    int id = create_ghost_cell(pair(mapId, listId));
    leak ghost_cell(id, _);
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

lemma void mem_counts_ok<t>(t x, int counterId)
    requires counts_ok<t>(?xs, ?entries) &*& mem(pair(x, counterId), entries) == true &*& [?f]ghost_counter_ticket(counterId);
    ensures counts_ok<t>(xs, entries) &*& [f]ghost_counter_ticket(counterId) &*& mem(x, xs) == true;
{
    open counts_ok(_, _);
    assert entries == cons(?p, ?entries0);
    if (p == pair(x, counterId)) {
        ghost_counter_match_ticket(counterId);
        count_eq_mem(x, xs);
    } else {
        mem_counts_ok(x, counterId);
    }
    close counts_ok(xs, entries);
}

lemma void ghost_list_match<t>()
    requires ghost_list<t>(?id, ?xs) &*& [?f]ghost_list_member_handle<t>(id, ?x);
    ensures ghost_list<t>(id, xs) &*& [f]ghost_list_member_handle<t>(id, x) &*& mem(x, xs) == true;
{
    open ghost_list(id, xs);
    assert [_]ghost_cell(id, pair(?mapId, ?listId));
    open ghost_list_member_handle(id, x);
    assert [_]ghost_map_entry_handle(mapId, x, ?counterId);
    ghost_map_match(mapId, x);
    mem_counts_ok(x, counterId);
    close [f]ghost_list_member_handle(id, x);
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

lemma void counts_ok_insert<t>(list<t> xs0, list<t> xs1, t x)
    requires counts_ok<t>(append(xs0, xs1), ?entries);
    ensures counts_ok<t>(append(xs0, cons(x, xs1)), entries);
{
    open counts_ok(_, _);
    switch (entries) {
        case nil:
        case cons(p, entries0):
            assert p == pair(?x1, ?counterId1);
            count_eq_append(x1, xs0, xs1);
            count_eq_append(x1, xs0, cons(x, xs1));
            counts_ok_insert(xs0, xs1, x);
    }
    close counts_ok<t>(append(xs0, cons(x, xs1)), entries);
}

lemma void counts_ok_insert_existing<t>(list<t> xs0, list<t> xs1, t x, int counterId)
    requires counts_ok<t>(append(xs0, xs1), ?entries) &*& mem(pair(x, counterId), entries) == true;
    ensures counts_ok<t>(append(xs0, cons(x, xs1)), entries) &*& ghost_counter_ticket(counterId);
{
    open counts_ok(_, _);
    assert entries == cons(pair(?x1, ?counterId1), ?entries0);
    count_eq_append(x1, xs0, xs1);
    count_eq_append(x1, xs0, cons(x, xs1));
    if (pair(x1, counterId1) == pair(x, counterId)) {
        create_ghost_counter_ticket(counterId1);
        counts_ok_insert(xs0, xs1, x);
    } else {
        counts_ok_insert_existing(xs0, xs1, x, counterId);
    }
    close counts_ok<t>(append(xs0, cons(x, xs1)), entries);
}

lemma int counts_ok_insert_new<t>(list<t> xs0, list<t> xs1, t x)
    requires counts_ok<t>(append(xs0, xs1), ?entries) &*& !mem(x, map(fst, entries));
    ensures counts_ok<t>(append(xs0, cons(x, xs1)), append(entries, {pair(x, result)})) &*& ghost_counter_ticket(result);
{
    open counts_ok(_, _);
    int result;
    switch (entries) {
        case nil:
            int counterId = create_ghost_counter();
            create_ghost_counter_ticket(counterId);
            result = counterId;
            count_eq_append(x, xs0, xs1);
            count_eq_nonnegative(x, append(xs0, xs1));
            count_eq_append(x, xs0, cons(x, xs1));
        case cons(p, entries0):
            assert p == pair(?x1, ?counterId1);
            count_eq_append(x1, xs0, xs1);
            count_eq_append(x1, xs0, cons(x, xs1));
            result = counts_ok_insert_new(xs0, xs1, x);
    }
    close counts_ok<t>(append(xs0, cons(x, xs1)), append(entries, {pair(x, result)}));
    return result;
}

lemma void ghost_list_insert<t>(int id, list<t> xs0, list<t> xs1, t x)
    requires ghost_list<t>(id, append(xs0, xs1));
    ensures ghost_list<t>(id, append(xs0, cons(x, xs1))) &*& ghost_list_member_handle<t>(id, x);
{
    open ghost_list<t>(_, _);
    assert [_]ghost_cell(id, pair(?mapId, ?listId));
    ghost_cell_mutate(listId, append(xs0, cons(x, xs1)));
    assert ghost_map(mapId, ?entries);
    if (mem(x, map(fst, entries))) {
        int counterId = ghost_map_get_entry_handle(mapId, x);
        counts_ok_insert_existing(xs0, xs1, x, counterId);
    } else {
        int counterId = counts_ok_insert_new(xs0, xs1, x);
        ghost_map_add(mapId, x, counterId);
    }
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

lemma void counts_ok_remove0<t>(list<t> xs0, list<t> xs1, t x)
    requires counts_ok<t>(append(xs0, cons(x, xs1)), ?entries) &*& !mem(x, map(fst, entries));
    ensures counts_ok<t>(append(xs0, xs1), entries);
{
    open counts_ok(_, _);
    switch (entries) {
        case nil:
        case cons(p, entries0):
            assert p == pair(?x1, ?counterId1);
            counts_ok_remove0(xs0, xs1, x);
            count_eq_append(x1, xs0, cons(x, xs1));
            count_eq_append(x1, xs0, xs1);
    }
    close counts_ok<t>(append(xs0, xs1), entries);
}

lemma void counts_ok_remove<t>(list<t> xs0, list<t> xs1, t x, int counterId)
    requires
        counts_ok<t>(append(xs0, cons(x, xs1)), ?entries) &*&
        distinct(map(fst, entries)) == true &*&
        mem(pair(x, counterId), entries) == true &*&
        ghost_counter_ticket(counterId);
    ensures
        counts_ok<t>(append(xs0, xs1), entries);
{
    open counts_ok(_, _);
    assert entries == cons(pair(?x1, ?counterId1), ?entries0);
    count_eq_append(x1, xs0, cons(x, xs1));
    count_eq_append(x1, xs0, xs1);
    if (pair(x1, counterId1) == pair(x, counterId)) {
        ghost_counter_destroy_ticket(counterId);
        counts_ok_remove0(xs0, xs1, x);
    } else {
        mem_map(pair(x, counterId), entries0, fst);
        assert x1 != x;
        counts_ok_remove(xs0, xs1, x, counterId);
    }
    close counts_ok<t>(append(xs0, xs1), entries);
}

lemma void ghost_list_remove<t>(int id, list<t> xs0, list<t> xs1, t x)
    requires ghost_list<t>(id, append(xs0, cons(x, xs1))) &*& ghost_list_member_handle<t>(id, x);
    ensures ghost_list<t>(id, append(xs0, xs1));
{
    open ghost_list(_, _);
    assert [_]ghost_cell(id, pair(?mapId, ?listId));
    open ghost_list_member_handle(_, _);
    assert [_]ghost_map_entry_handle(mapId, x, ?counterId);
    ghost_map_match(mapId, x);
    ghost_map_keys_distinct(mapId);
    counts_ok_remove(xs0, xs1, x, counterId);
    ghost_cell_mutate(listId, append(xs0, xs1));
}

@*/

