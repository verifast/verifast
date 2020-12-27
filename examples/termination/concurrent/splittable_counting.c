//@ #include "splittable_counting.gh"
//@ #include "atomics.gh"
//@ #include "ghost_cells.gh"
//@ #include "ghost_lists.gh"

/*@

fixpoint real real_sum(list<real> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return x + real_sum(xs0);
    }
}

fixpoint bool real_lt(real x, real y) { return x < y; }

fixpoint int sum(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return x + sum(xs0);
    }
}

predicate counting_handle_id_reservation(int id) =
    ghost_cell<pair<int, int> >(id, pair(0, 0));

predicate_ctor counting_inv(int id, predicate(;) p)() =
    [_]ghost_cell<pair<int, int> >(id, pair(?handlesId, ?ticketsId)) &*&
    ghost_list<real>(ticketsId, ?tickets) &*& forall(tickets, (real_lt)(0)) == true &*& real_sum(tickets) < 1 &*&
    [1 - real_sum(tickets)]p() &*&
    ghost_list<pair<real, int> >(handlesId, ?handles) &*& forall(map(fst, handles), (real_lt)(0)) && real_sum(map(fst, handles)) == 1 && sum(map(snd, handles)) == length(tickets);

predicate counting_handle(int id, predicate(;) p, real frac, int tickets) =
    [frac]atomic_space(0, counting_inv(id, p)) &*&
    [_]ghost_cell<pair<int, int> >(id, pair(?handlesId, ?ticketsId)) &*&
    ghost_list_member_handle<pair<real, int> >(handlesId, pair(frac, tickets));

predicate counting_ticket(int id, real frac) =
    [_]ghost_cell<pair<int, int> >(id, pair(?handlesId, ?ticketsId)) &*&
    ghost_list_member_handle<real>(ticketsId, frac);

lemma int create_counting_handle_id_reservation()
    requires true;
    ensures counting_handle_id_reservation(result);
{
    int id = create_ghost_cell<pair<int, int> >(pair(0, 0));
    close counting_handle_id_reservation(id);
    return id;
}

lemma void create_counting_handle(predicate(;) p)
    requires counting_handle_id_reservation(?id) &*& p();
    ensures counting_handle(id, p, 1, 0);
{
    open counting_handle_id_reservation(id);
    int handlesId = create_ghost_list<pair<real, int> >();
    int ticketsId = create_ghost_list<real>();
    ghost_list_insert(handlesId, nil, nil, pair(1r, 0));
    ghost_cell_mutate(id, pair(handlesId, ticketsId));
    leak ghost_cell(id, _);
    close counting_inv(id, p)();
    create_atomic_space(0, counting_inv(id, p));
    close counting_handle(id, p, 1, 0);
}

lemma pair<list<pair<real, int> >, list<pair<real, int> > > remove_handle_helper(real frac, int tickets, list<pair<real, int> > handles)
    requires forall(map(fst, handles), (real_lt)(0)) == true &*& mem(pair(frac, tickets), handles) == true;
    ensures
        handles == append(fst(result), cons(pair(frac, tickets), snd(result))) &*&
        0 < frac &*&
        remove(pair(frac, tickets), handles) == append(fst(result), snd(result)) &*&
        forall(map(fst, remove(pair(frac, tickets), handles)), (real_lt)(0)) == true &*&
        real_sum(map(fst, remove(pair(frac, tickets), handles))) + frac == real_sum(map(fst, handles)) &*&
        sum(map(snd, remove(pair(frac, tickets), handles))) + tickets == sum(map(snd, handles));
{
    switch (handles) {
        case nil:
        case cons(h, hs1):
            assert h == pair(?f, ?ts);
            if (h == pair(frac, tickets)) {
                return pair(nil, hs1);
            } else {
                pair<list<pair<real, int> >, list<pair<real, int> > > hs11_hs12 = remove_handle_helper(frac, tickets, hs1);
                assert hs11_hs12 == pair(?hs11, ?hs12);
                return pair(cons(h, hs11), hs12);
            }
    }
}

lemma void split_counting_handle(int id, real frac1, int tickets1)
    nonghost_callers_only
    requires counting_handle(id, ?p, ?f, ?tickets) &*& 0 < frac1 &*& frac1 < f;
    ensures counting_handle(id, p, frac1, tickets1) &*& counting_handle(id, p, f - frac1, tickets - tickets1);
{
    open counting_handle(id, p, f, tickets);
    assert [_]ghost_cell<pair<int, int> >(id, pair(?handlesId, ?ticketsId));
    {
        predicate P() =
            [_]ghost_cell<pair<int, int> >(id, pair(handlesId, ticketsId)) &*&
            ghost_list_member_handle<pair<real, int> >(handlesId, pair(f, tickets));
        predicate Q() =
            ghost_list_member_handle<pair<real, int> >(handlesId, pair(frac1, tickets1)) &*&
            ghost_list_member_handle<pair<real, int> >(handlesId, pair(f - frac1, tickets - tickets1));
        lemma void op()
            requires counting_inv(id, p)() &*& P();
            ensures counting_inv(id, p)() &*& Q();
        {
            open counting_inv(id, p)();
            open P();
            assert ghost_list<pair<real, int> >(handlesId, ?handles);
            ghost_list_match<pair<real, int> >();
            pair<list<pair<real, int> >, list<pair<real, int> > > handles1_handles2 = remove_handle_helper(f, tickets, handles);
            assert handles1_handles2 == pair(?handles1, ?handles2);
            ghost_list_remove(handlesId, handles1, handles2, pair(f, tickets));
            ghost_list_insert(handlesId, nil, append(handles1, handles2), pair(frac1, tickets1));
            ghost_list_insert(handlesId, nil, cons(pair(frac1, tickets1), append(handles1, handles2)), pair(f - frac1, tickets - tickets1));
            close Q();
            close counting_inv(id, p)();
        }
        produce_lemma_function_pointer_chunk(op) : atomic_noop_body(0, counting_inv(id, p), P, Q)() { call(); } {
            close P();
            atomic_noop();
            open Q();
        }
    }
    close counting_handle(id, p, frac1, tickets1);
    close counting_handle(id, p, f - frac1, tickets - tickets1);
}

lemma void ghost_list_match_<t>(t x)
    requires ghost_list<t>(?id, ?xs) &*& [?f]ghost_list_member_handle<t>(id, x);
    ensures ghost_list<t>(id, xs) &*& [f]ghost_list_member_handle<t>(id, x) &*& mem(x, xs) == true;
{
    ghost_list_match();
}

lemma void merge_counting_handle(int id)
    nonghost_callers_only
    requires counting_handle(id, ?p, ?f1, ?tickets1) &*& counting_handle(id, p, ?f2, ?tickets2);
    ensures counting_handle(id, p, f1 + f2, tickets1 + tickets2);
{
    open counting_handle(id, p, f1, tickets1);
    open counting_handle(id, p, f2, tickets2);
    assert [_]ghost_cell<pair<int, int> >(id, pair(?handlesId, ?ticketsId));
    {
        predicate P() =
            [_]ghost_cell<pair<int, int> >(id, pair(handlesId, ticketsId)) &*&
            ghost_list_member_handle<pair<real, int> >(handlesId, pair(f1, tickets1)) &*&
            ghost_list_member_handle<pair<real, int> >(handlesId, pair(f2, tickets2));
        predicate Q() =
            ghost_list_member_handle<pair<real, int> >(handlesId, pair(f1 + f2, tickets1 + tickets2));
        lemma void op()
            requires counting_inv(id, p)() &*& P();
            ensures counting_inv(id, p)() &*& Q();
        {
            open counting_inv(id, p)();
            open P();
            assert ghost_list<pair<real, int> >(handlesId, ?handles);
            ghost_list_match_(pair(f1, tickets1));
            pair<list<pair<real, int> >, list<pair<real, int> > > handles1_handles2 = remove_handle_helper(f1, tickets1, handles);
            assert handles1_handles2 == pair(?handles1, ?handles2);
            ghost_list_remove(handlesId, handles1, handles2, pair(f1, tickets1));

            assert ghost_list<pair<real, int> >(handlesId, ?handles_);
            ghost_list_match_(pair(f2, tickets2));
            pair<list<pair<real, int> >, list<pair<real, int> > > handles3_handles4 = remove_handle_helper(f2, tickets2, handles_);
            assert handles3_handles4 == pair(?handles3, ?handles4);
            ghost_list_remove(handlesId, handles3, handles4, pair(f2, tickets2));
            
            assert ghost_list<pair<real, int> >(handlesId, ?handles__);
            ghost_list_insert(handlesId, nil, handles__, pair(f1 + f2, tickets1 + tickets2));
            close Q();
            close counting_inv(id, p)();
        }
        produce_lemma_function_pointer_chunk(op) : atomic_noop_body(0, counting_inv(id, p), P, Q)() { call(); } {
            close P();
            atomic_noop();
            open Q();
        }
    }
    close counting_handle(id, p, f1 + f2, tickets1 + tickets2);
}

lemma void create_counting_ticket(int id)
    nonghost_callers_only
    requires counting_handle(id, ?p, ?f, ?tickets);
    ensures counting_handle(id, p, f, tickets + 1) &*& counting_ticket(id, ?frac) &*& [frac]p() &*& 0 < frac;
{
    open counting_handle(id, p, f, tickets);
    assert [_]ghost_cell<pair<int, int> >(id, pair(?handlesId, ?ticketsId));
    {
        predicate P() =
            [_]ghost_cell<pair<int, int> >(id, pair(handlesId, ticketsId)) &*&
            ghost_list_member_handle<pair<real, int> >(handlesId, pair(f, tickets));
        predicate Q() =
            ghost_list_member_handle<pair<real, int> >(handlesId, pair(f, tickets + 1)) &*&
            ghost_list_member_handle<real>(ticketsId, ?frac) &*& [frac]p() &*& 0 < frac;
        lemma void op()
            requires counting_inv(id, p)() &*& P();
            ensures counting_inv(id, p)() &*& Q();
        {
            open counting_inv(id, p)();
            open P();
            assert ghost_list<pair<real, int> >(handlesId, ?handles);
            ghost_list_match<pair<real, int> >();
            pair<list<pair<real, int> >, list<pair<real, int> > > handles1_handles2 = remove_handle_helper(f, tickets, handles);
            assert handles1_handles2 == pair(?handles1, ?handles2);
            ghost_list_remove(handlesId, handles1, handles2, pair(f, tickets));
            ghost_list_insert(handlesId, nil, append(handles1, handles2), pair(f, tickets + 1));
            assert ghost_list<real>(ticketsId, ?tickets_);
            real frac = (1 - real_sum(tickets_)) / 2;
            ghost_list_insert(ticketsId, nil, tickets_, frac);
            close Q();
            close counting_inv(id, p)();
        }
        produce_lemma_function_pointer_chunk(op) : atomic_noop_body(0, counting_inv(id, p), P, Q)() { call(); } {
            close P();
            atomic_noop();
            open Q();
        }
    }
    close counting_handle(id, p, f, tickets + 1);
    close counting_ticket(id, _);
}

lemma pair<list<real>, list<real> > remove_ticket_helper(real frac, list<real> tickets)
    requires mem(frac, tickets) == true &*& forall(tickets, (real_lt)(0)) == true;
    ensures
        tickets == append(fst(result), cons(frac, snd(result))) &*& remove(frac, tickets) == append(fst(result), snd(result)) &*&
        real_sum(remove(frac, tickets)) + frac == real_sum(tickets) &*&
        forall(remove(frac, tickets), (real_lt)(0)) == true &*& 0 < frac;
{
    switch (tickets) {
        case nil:
        case cons(t, ts):
            if (t == frac) {
                return pair(nil, ts);
            } else {
                pair<list<real>, list<real> > ts1_ts2 = remove_ticket_helper(frac, ts);
                assert ts1_ts2 == pair(?ts1, ?ts2);
                return pair(cons(t, ts1), ts2);
            }
    }
}

lemma void destroy_counting_ticket(int id)
    nonghost_callers_only
    requires counting_handle(id, ?p, ?f, ?tickets) &*& counting_ticket(id, ?frac) &*& [frac]p();
    ensures counting_handle(id, p, f, tickets - 1);
{
    open counting_handle(id, p, f, tickets);
    open counting_ticket(id, frac);
    assert [_]ghost_cell<pair<int, int> >(id, pair(?handlesId, ?ticketsId));
    {
        predicate P() =
            [_]ghost_cell<pair<int, int> >(id, pair(handlesId, ticketsId)) &*&
            ghost_list_member_handle<pair<real, int> >(handlesId, pair(f, tickets)) &*&
            ghost_list_member_handle<real>(ticketsId, frac) &*& [frac]p();
        predicate Q() =
            ghost_list_member_handle<pair<real, int> >(handlesId, pair(f, tickets - 1));
        lemma void op()
            requires counting_inv(id, p)() &*& P();
            ensures counting_inv(id, p)() &*& Q();
        {
            open counting_inv(id, p)();
            open P();
            assert ghost_list<pair<real, int> >(handlesId, ?handles);
            ghost_list_match<pair<real, int> >();
            pair<list<pair<real, int> >, list<pair<real, int> > > handles1_handles2 = remove_handle_helper(f, tickets, handles);
            assert handles1_handles2 == pair(?handles1, ?handles2);
            ghost_list_remove(handlesId, handles1, handles2, pair(f, tickets));
            ghost_list_insert(handlesId, nil, append(handles1, handles2), pair(f, tickets - 1));
            assert ghost_list<real>(ticketsId, ?tickets_);
            ghost_list_match_(frac);
            pair<list<real>, list<real> > ts1_ts2 = remove_ticket_helper(frac, tickets_);
            assert ts1_ts2 == pair(?ts1, ?ts2);
            ghost_list_remove(ticketsId, ts1, ts2, frac);
            close Q();
            close counting_inv(id, p)();
        }
        produce_lemma_function_pointer_chunk(op) : atomic_noop_body(0, counting_inv(id, p), P, Q)() { call(); } {
            close P();
            atomic_noop();
            open Q();
        }
    }
    close counting_handle(id, p, f, tickets - 1);
}

lemma void real_lt_trans(real x, real y, real z)
    requires x < y && y < z;
    ensures x < z;
{}

lemma void destroy_counting_handle_helper(list<pair<real, int> > handles)
    requires forall(map(fst, handles), (real_lt)(0)) && real_sum(map(fst, handles)) <= 0;
    ensures handles == nil;
{
    switch (handles) {
        case nil:
        case cons(h, hs):
            destroy_counting_handle_helper(hs);
            assert false;
    }
}

lemma void destroy_counting_handle(int id)
    nonghost_callers_only
    requires counting_handle(id, ?p, 1, 0);
    ensures p();
{
    open counting_handle(id, p, 1, 0);
    atomic_space_destroy(0, counting_inv(id, p));
    open counting_inv(id, p)();
    ghost_list_match_(pair(1r, 0));
    assert ghost_list<pair<real, int> >(?handlesId, ?handles);
    pair<list<pair<real, int> >, list<pair<real, int> > > hs1_hs2 = remove_handle_helper(1, 0, handles);
    assert hs1_hs2 == pair(?hs1, ?hs2);
    ghost_list_remove(handlesId, hs1, hs2, pair(1r, 0));
    assert ghost_list<pair<real, int> >(handlesId, ?handles_);
    destroy_counting_handle_helper(handles_);
    assert ghost_list<real>(?ticketsId, ?tickets);
    switch (tickets) { case nil: case cons(h, t): }
    leak ghost_list(_, _) &*& ghost_list(_, _);
}

@*/