//@ #include "listex.gh"
//@ #include "nat.gh"
//@ #include "ghost_cells.gh"
//@ #include "raw_ghost_lists_.gh"
//@ #include "precision_axiom.gh"
//@ #include "ghost_counters.gh"

/*@

predicate_ctor chunk(int id)(pair<real, int> info;) =
    info == pair(?f, ?k) &*& 0 < f &*& [f]raw_ghost_list_member_handle<unit>(id, k, unit);

fixpoint real real_of_nat(nat n) {
    switch (n) {
        case zero: return 0;
        case succ(n0): return 1 + real_of_nat(n0);
    }
}

fixpoint real real_of_int(int x) { return 0 <= x ? real_of_nat(nat_of_int(x)) : -real_of_nat(nat_of_int(-x)); }

fixpoint real real_sum(list<real> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return x + real_sum(xs0);
    }
}

predicate ghost_counter(int id; int count) =
    [_]ghost_cell(id, pair(?listId, pair(?countId, ?destroyedChunksId))) &*&
    ghost_cell(countId, count) &*&
    raw_ghost_list<unit>(listId, ?n, ?elems) &*& length(elems) == n &*&
    0 <= count &*& count <= n &*&
    ghost_cell(destroyedChunksId, ?destroyedChunks) &*&
    foreachp(destroyedChunks, chunk(listId)) &*& real_sum(map(fst, destroyedChunks)) == real_of_int(n - count);

predicate ghost_counter_ticket_(real frac, int id, unit u) =
    0 < frac &*&
    [_]ghost_cell<pair<int, pair<int, int> > >(id, pair(?listId, _)) &*&
    exists<list<pair<real, int> > >(?chunks) &*& foreachp(chunks, chunk(listId)) &*& frac == real_sum(map(fst, chunks));

lemma void note(bool b)
    requires b;
    ensures b;
{}

lemma void real_lt_trans(real x, real y, real z)
    requires x < y && y < z;
    ensures x < z;
{}

lemma void split(real f1, real f2)
    requires 0 < f1 &*& 0 < f2 &*& ghost_counter_ticket_(f1 + f2, ?id, ?u);
    ensures ghost_counter_ticket_(f1, id, u) &*& ghost_counter_ticket_(f2, id, u);
{
    open ghost_counter_ticket_(_, _, _);
    assert [_]ghost_cell(id, pair(?listId, _));
    open exists<list<pair<real, int> > >(?chunks);
    assert chunks == cons(pair(?f, ?k), ?tail);
    list<pair<real, int> > chunks1 = nil;
    list<pair<real, int> > chunks2 = tail;
    open foreachp(chunks, chunk(listId));
    open chunk(listId)(pair(f, k));
    while (real_sum(map(fst, chunks2)) > f2)
        invariant
            foreachp(chunks1, chunk(listId)) &*& 0 < f &*& [f]raw_ghost_list_member_handle<unit>(listId, k, unit) &*& foreachp(chunks2, chunk(listId)) &*&
            real_sum(map(fst, chunks1)) < f1 &*& real_sum(map(fst, chunks1)) + f + real_sum(map(fst, chunks2)) == f1 + f2;
        decreases length(chunks2);
    {
        chunks1 = cons(pair(f, k), chunks1);
        close chunk(listId)(pair(f, k));
        close foreachp(chunks1, chunk(listId));
        open foreachp(chunks2, chunk(listId));
        real_lt_trans(0, f2, real_sum(map(fst, chunks2)));
        assert chunks2 == cons(pair(?f_, ?k_), ?chunks2_);
        f = f_;
        k = k_;
        chunks2 = chunks2_;
        open chunk(listId)(pair(f, k));
    }
    if (real_sum(map(fst, chunks2)) == f2) {
        chunks1 = cons(pair(f, k), chunks1);
        close chunk(listId)(pair(f, k));
        close foreachp(chunks1, chunk(listId));
    } else {
        chunks1 = cons(pair(f1 - real_sum(map(fst, chunks1)), k), chunks1);
        close chunk(listId)(head(chunks1));
        chunks2 = cons(pair(f2 - real_sum(map(fst, chunks2)), k), chunks2);
        close chunk(listId)(head(chunks2));
        close foreachp(chunks1, chunk(listId));
        close foreachp(chunks2, chunk(listId));
    }
    close exists(chunks1);
    close ghost_counter_ticket_(f1, id, u);
    close exists(chunks2);
    close ghost_counter_ticket_(f2, id, u);
}

lemma void merge()
    requires ghost_counter_ticket_(?f1, ?id, ?u1) &*& ghost_counter_ticket_(?f2, id, ?u2);
    ensures ghost_counter_ticket_(f1 + f2, id, u1) &*& u2 == u1;
{
    switch (u1) { case unit: }
    switch (u2) { case unit: }
    open ghost_counter_ticket_(f1, id, u1);
    assert [_]ghost_cell(id, pair(?listId, _));
    open exists(?chunks1);
    open ghost_counter_ticket_(f2, id, u2);
    open exists(?chunks2);
    while (chunks1 != nil)
        invariant foreachp(chunks1, chunk(listId)) &*& foreachp(chunks2, chunk(listId)) &*& real_sum(map(fst, chunks1)) + real_sum(map(fst, chunks2)) == f1 + f2;
        decreases length(chunks1);
    {
        assert chunks1 == cons(pair(?f, ?k), ?chunks1_);
        open foreachp(chunks1, chunk(listId));
        chunks1 = chunks1_;
        chunks2 = cons(pair(f, k), chunks2);
        close foreachp(chunks2, chunk(listId));
    }
    close exists(chunks2);
    close ghost_counter_ticket_(f1 + f2, id, u1);
}

predicate ghost_counter_ticket(int id;) =
    precise(ghost_counter_ticket_, id, _);

lemma int create_ghost_counter()
    requires true;
    ensures ghost_counter(result, 0);
{
    int listId = create_raw_ghost_list<unit>();
    int countId = create_ghost_cell<int>(0);
    int destroyedChunksId = create_ghost_cell<list<pair<real, int> > >(nil);
    int id = create_ghost_cell<pair<int, pair<int, int> > >(pair(listId, pair(countId, destroyedChunksId)));
    leak ghost_cell(id, _);
    return id;
}

lemma void create_ghost_counter_ticket(int id)
    requires ghost_counter(id, ?n);
    ensures ghost_counter(id, n + 1) &*& ghost_counter_ticket(id);
{
    open ghost_counter(id, n);
    assert [_]ghost_cell(id, pair(?listId, pair(?countId, ?destroyedChunksId)));
    ghost_cell_mutate(countId, n + 1);
    raw_ghost_list_add(listId, unit);
    assert raw_ghost_list_member_handle(listId, ?k, _);
    close exists({pair(1r, k)});
    close chunk(listId)(pair(1r, k));
    close ghost_counter_ticket_(1, id, unit);
    produce_lemma_function_pointer_chunk(split) : split<int, unit>(ghost_counter_ticket_)(f1, f2) { call(); } {
        produce_lemma_function_pointer_chunk(merge) : merge<int, unit>(ghost_counter_ticket_)() { call(); } {
            close_precise(1, ghost_counter_ticket_, id, unit);
        }
    }
}

lemma void chunks_range(int id, list<pair<real, int> > chunks)
    requires raw_ghost_list<unit>(id, ?n, ?elems) &*& foreachp(chunks, chunk(id));
    ensures raw_ghost_list<unit>(id, n, elems) &*& foreachp(chunks, chunk(id)) &*& forall(map(snd, chunks), (contains)(map(fst, elems))) == true;
{
    switch (chunks) {
        case nil:
        case cons(c, cs):
            assert c == pair(?f, ?k);
            open foreachp(chunks, chunk(id));
            chunks_range(id, cs);
            open chunk(id)(pair(f, k));
            assert [_]raw_ghost_list_member_handle(id, k, ?u);
            raw_ghost_list_match(id, k);
            mem_map(pair(k, u), elems, fst);
            close chunk(id)(pair(f, k));
    }
}   

lemma void sum_raw_ghost_list_member_handle_fracs_lt_n(int id, list<pair<real, int> > chunks, list<int> ks)
    requires raw_ghost_list<unit>(id, ?n, ?elems) &*& foreachp(chunks, chunk(id)) &*& forall(map(snd, chunks), (contains)(ks)) == true;
    ensures real_sum(map(fst, chunks)) <= real_of_int(length(ks));
{
    switch (ks) {
        case nil:
            switch (chunks) { case nil: case cons(h, t): }
            leak raw_ghost_list(_, _, _) &*& foreachp(_, _);
        case cons(k, ks0):
            real f0 = real_sum(map(fst, chunks));
            list<pair<real, int> > chunks1 = nil;
            real f = 0;
            while (chunks != nil)
                invariant foreachp(chunks, chunk(id)) &*& 0 <= f &*& (f == 0 ? true : [f]raw_ghost_list_member_handle<unit>(id, k, _)) &*&
                    foreachp(chunks1, chunk(id)) &*&
                    real_sum(map(fst, chunks)) + f + real_sum(map(fst, chunks1)) == f0 &*&
                    forall(map(snd, chunks), (contains)(ks)) == true &*&
                    forall(map(snd, chunks1), (contains)(ks0)) == true;
                decreases length(chunks);
            {
                assert chunks == cons(pair(?f1, ?k1), ?tail);
                open foreachp(chunks, chunk(id));
                chunks = tail;
                if (k1 == k) {
                    open chunk(id)(pair(f1, k1));
                    f += f1;
                } else {
                    chunks1 = cons(pair(f1, k1), chunks1);
                    close foreachp(chunks1, chunk(id));
                }
            }
            if (f != 0) {
                raw_ghost_list_match(id, k);
                leak [_]raw_ghost_list_member_handle(_, _, _);
            }
            assert f <= 1;
            succ_int(length(ks0));
            sum_raw_ghost_list_member_handle_fracs_lt_n(id, chunks1, ks0);
            note(f0 - f <= real_of_int(length(ks0)));
            note(real_of_int(length(ks)) == real_of_int(length(ks0)) + 1);
    }
}

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

lemma void raw_ghost_list_remove_elems()
    requires raw_ghost_list<unit>(?id, ?n, ?elems) &*& foreachp(?cs, chunk(id)) &*& real_sum(map(fst, cs)) == real_of_int(length(elems));
    ensures raw_ghost_list<unit>(id, n, nil);
{
    while (elems != nil)
        invariant raw_ghost_list(id, n, elems) &*& foreachp(cs, chunk(id)) &*& real_sum(map(fst, cs)) == real_of_int(length(elems));
        decreases length(elems);
    {
        real f0 = real_sum(map(fst, cs));
        assert elems == cons(pair(?k, ?u), ?elems0);
        unit u_ = u;
        switch (u_) { case unit: }
        list<pair<real, int> > cs1 = nil;
        real f = 0;
        chunks_range(id, cs);
        while (cs != nil)
            invariant
                foreachp(cs, chunk(id)) &*& forall(map(snd, cs), (contains)(map(fst, elems))) == true &*&
                0 <= f &*& (f == 0 ? true : [f]raw_ghost_list_member_handle<unit>(id, k, u)) &*&
                foreachp(cs1, chunk(id)) &*& forall(map(snd, cs1), (contains)(map(fst, elems0))) == true &*&
                real_sum(map(fst, cs)) + f + real_sum(map(fst, cs1)) == f0;
            decreases length(cs);
        {
            assert cs == cons(pair(?f1, ?k1), ?cs0);
            open foreachp(cs, chunk(id));
            cs = cs0;
            if (k1 == k) {
                f += f1;
                open chunk(id)(pair(f1, k1));
            } else {
                cs1 = cons(pair(f1, k1), cs1);
                close foreachp(cs1, chunk(id));
            }
        }
        if (!(real_sum(map(fst, cs1)) <= real_of_int(length(map(fst, elems0)))))
            sum_raw_ghost_list_member_handle_fracs_lt_n(id, cs1, map(fst, elems0));
        length_map(fst, elems0);
        assert length(elems) == 1 + length(map(fst, elems0));
        succ_int(length(elems0));
        raw_ghost_list_match(id, k);
        assert f == 1;
        raw_ghost_list_remove(id, k);
        cs = cs1;
        elems = elems0;
    }
    leak foreachp(_, _);
}

lemma void ghost_counter_match_ticket(int id)
    requires ghost_counter(id, ?count) &*& [?f]ghost_counter_ticket(id);
    ensures ghost_counter(id, count) &*& [f]ghost_counter_ticket(id) &*& 0 < count;
{
    open ghost_counter(_, _);
    assert [_]ghost_cell(id, pair(?listId, pair(?countId, ?destroyedChunksId)));
    if (count == 0) {
        raw_ghost_list_remove_elems();
        
        open ghost_counter_ticket(_);
        open_precise(f, ghost_counter_ticket_, id);
        open ghost_counter_ticket_(f, id, _);
        open exists(?chunks);
        assert chunks == cons(pair(?fc, ?kc), ?tail);
        open foreachp(chunks, chunk(listId));
        open chunk(listId)(pair(fc, kc));
        raw_ghost_list_match(listId, kc);
        assert false;
    }
}

lemma void ghost_counter_destroy_ticket(int id)
    requires ghost_counter(id, ?count) &*& ghost_counter_ticket(id);
    ensures ghost_counter(id, count - 1) &*& 0 < count;
{
    ghost_counter_match_ticket(id);
    
    open ghost_counter(_, _);
    assert [_]ghost_cell(id, pair(?listId, pair(?countId, ?destroyedChunksId)));
    assert raw_ghost_list(listId, ?n, _);
    assert ghost_cell(destroyedChunksId, ?destroyedChunks);
    ghost_cell_mutate(countId, count - 1);
    
    open ghost_counter_ticket(_);
    open_precise(1, ghost_counter_ticket_, id);
    open ghost_counter_ticket_(1, id, _);
    open exists(?chunks);
    succ_int(n - count);
    
    while (chunks != nil)
        invariant foreachp(destroyedChunks, chunk(listId)) &*& foreachp(chunks, chunk(listId)) &*&
            real_sum(map(fst, destroyedChunks)) + real_sum(map(fst, chunks)) == real_of_int(n - (count - 1));
        decreases length(chunks);
    {
        assert chunks == cons(pair(?f, ?k), ?chunks0);
        open foreachp(chunks, chunk(listId));
        destroyedChunks = cons(pair(f, k), destroyedChunks);
        close foreachp(destroyedChunks, chunk(listId));
        chunks = chunks0;
    }
    
    ghost_cell_mutate(destroyedChunksId, destroyedChunks);
}

@*/