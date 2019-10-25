//@ #include <listex.gh>
//@ #include "ghost_cells.gh"
//@ #include "raw_ghost_lists.gh"
//@ #include "ghost_counters.gh"

/*@

predicate foreach2<a, b>(list<a> xs, predicate(a; b) p; list<b> ys) =
    switch (xs) {
        case nil: return ys == nil;
        case cons(x, xs0): return p(x, ?y) &*& foreach2(xs0, p, ?ys0) &*& ys == cons(y, ys0);
    };

predicate foreach2_mem_results<a, b>(list<a> xs_before, list<a> xs_after, list<b> ys_before, b y, list<b> ys_after) = true;

lemma void foreach2_mem<a, b>(a x)
    requires foreach2<a, b>(?xs, ?p, ?ys) &*& mem(x, xs) == true;
    ensures
        foreach2_mem_results<a, b>(?xs0, ?xs1, ?ys0, ?y, ?ys1) &*&
        xs == append(xs0, cons(x, xs1)) &*& ys == append(ys0, cons(y, ys1)) &*&
        remove(x, xs) == append(xs0, xs1) &*&
        foreach2(xs0, p, ys0) &*& p(x, y) &*& foreach2(xs1, p, ys1);
{
    open foreach2(xs, p, ys);
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                close foreach2_mem_results(nil, xs0, nil, head(ys), tail(ys));
                close foreach2(nil, p, nil);
            } else {
                foreach2_mem(x);
                open foreach2_mem_results(?xs00, ?xs1, ?ys00, ?y, ?ys1);
                close foreach2_mem_results(cons(x0, xs00), xs1, cons(head(ys), ys00), y, ys1);
                close foreach2(cons(x0, xs00), p, cons(head(ys), ys00));
            }
    }
}

lemma void foreach2_append<a, b>(list<a> xs0, list<a> xs1)
    requires foreach2<a, b>(xs0, ?p, ?ys0) &*& foreach2<a, b>(xs1, p, ?ys1);
    ensures foreach2<a, b>(append(xs0, xs1), p, append(ys0, ys1));
{
    open foreach2(xs0, p, ys0);
    switch (xs0) {
        case nil:
        case cons(x0, xs00):
            foreach2_append(xs00, xs1);
            close foreach2(append(xs0, xs1), p, append(ys0, ys1));
    }
}

inductive info = info(int tokenCell, int list);
inductive cinfo = cinfo(int contribCell, real tokenFrac);

predicate_ctor contrib(int tokenCell)(pair<int, cinfo> e; int c) =
    switch (e) {
        case pair(k, i): return
            switch (i) {
                case cinfo(contribCell, tokenFrac): return
                    [1/2]ghost_cell<int>(contribCell, c) &*& 0 <= c &*& [tokenFrac]ghost_cell<unit>(tokenCell, unit) &*& 0 < tokenFrac;
            };
    };

fixpoint int sum(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return x + sum(xs0);
    }
}

lemma void sum_append(list<int> xs, list<int> ys)
    requires true;
    ensures sum(append(xs, ys)) == sum(xs) + sum(ys);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            sum_append(xs0, ys);
    }
}

fixpoint bool nonneg(int x) { return 0 <= x; }

predicate ghost_counter(int id; int count) =
    [_]ghost_cell<info>(id, ?info) &*&
    switch (info) {
        case info(tokenCell, list): return
            raw_ghost_list(list, _, ?es) &*&
            foreach2(es, contrib(tokenCell), ?cs) &*&
            forall(cs, nonneg) == true &*&
            count == sum(cs);
    };

lemma void nonneg_sum(list<int> xs)
    requires forall(xs, nonneg) == true;
    ensures 0 <= sum(xs);
{
    switch (xs) {
    case nil:
    case cons(x, xs0):
        nonneg_sum(xs0);
    }
}

predicate ghost_counter_zero_contrib(int id;) =
    [_]ghost_cell<info>(id, ?info) &*&
    switch (info) {
        case info(tokenCell, list): return
            ghost_cell<unit>(tokenCell, unit);
    };

predicate ghost_counter_contrib(int id, real frac, int contrib) =
    [_]ghost_cell<info>(id, ?info) &*&
    switch (info) {
        case info(tokenCell, list): return
            0 <= contrib &*&
            contrib == 0 ?
                [frac]ghost_cell<unit>(tokenCell, unit)
            :
                raw_ghost_list_member_handle<cinfo>(list, _, ?cinfo) &*&
                switch (cinfo) {
                    case cinfo(contribCell, tokenFrac): return
                        [1/2]ghost_cell<int>(contribCell, contrib) &*&
                        frac == tokenFrac;
                };
    };

lemma int create_ghost_counter()
    requires true;
    ensures ghost_counter(result, 0) &*& ghost_counter_zero_contrib(result);
{
    int tokenCell = create_ghost_cell<unit>(unit);
    int list = create_raw_ghost_list<cinfo>();
    int id = create_ghost_cell<info>(info(tokenCell, list));
    ghost_cell_leak<info>(id);
    close foreach2(nil, contrib(tokenCell), nil);
    close ghost_counter(id, 0);
    close ghost_counter_zero_contrib(id);
    return id;
}

lemma void ghost_counter_start_contrib()
    requires [?f]ghost_counter_zero_contrib(?id);
    ensures ghost_counter_contrib(id, f, 0);
{
    open ghost_counter_zero_contrib(id);
    close ghost_counter_contrib(id, f, 0);
}

lemma void ghost_counter_increment()
    requires ghost_counter(?id, ?count) &*& ghost_counter_contrib(id, ?f, ?contrib);
    ensures ghost_counter(id, count + 1) &*& ghost_counter_contrib(id, f, contrib + 1);
{
    open ghost_counter(id, count);
    open ghost_counter_contrib(id, f, contrib);
    assert [_]ghost_cell<info>(id, ?info);
    switch (info) {
        case info(tokenCell, list):
            if (contrib == 0) {
                assert raw_ghost_list(list, ?n, ?es);
                int contribCell = create_ghost_cell<int>(0);
                raw_ghost_list_add(list, cinfo(contribCell, f));
                pair<int, cinfo> e = pair(n, cinfo(contribCell, f));
                ghost_cell_fraction_info<unit>(tokenCell);
                close contrib(tokenCell)(e, 0);
                assert foreach2(es, _, ?cs);
                close foreach2(nil, contrib(tokenCell), nil);
                close foreach2(cons(e, nil), contrib(tokenCell), cons(0, nil));
                foreach2_append(es, cons(e, nil));
                sum_append(cs, cons(0, nil));
                forall_append(cs, cons(0, nil), nonneg);
            }
            assert raw_ghost_list_member_handle<cinfo>(list, ?k, ?cinfo);
            raw_ghost_list_match(list, k);
            foreach2_mem(pair(k, cinfo));
            open foreach2_mem_results<pair<int, cinfo>, int>(?es0, ?es1, ?cs0, ?c, ?cs1);
            open contrib(tokenCell)(pair(k, cinfo), c);
            switch (cinfo) {
                case cinfo(contribCell, tokenFrac):
                    ghost_cell_mutate<int>(contribCell, contrib + 1);
                    close contrib(tokenCell)(pair(k, cinfo), c + 1);
                    close foreach2(cons(pair(k, cinfo), es1), contrib(tokenCell), cons(c + 1, cs1));
                    foreach2_append(es0, cons(pair(k, cinfo), es1));
                    sum_append(cs0, cons(c + 1, cs1));
                    sum_append(cs0, cons(c, cs1));
                    forall_append(cs0, cons(c, cs1), nonneg);
                    forall_append(cs0, cons(c + 1, cs1), nonneg);
                    close ghost_counter(id, count + 1);
                    close ghost_counter_contrib(id, f, contrib + 1);
            }
    }
}

lemma void ghost_counter_decrement()
    requires ghost_counter(?id, ?count) &*& ghost_counter_contrib(id, ?f, ?contrib) &*& 0 < contrib;
    ensures ghost_counter(id, count - 1) &*& ghost_counter_contrib(id, f, contrib - 1) &*& 0 < count;
{
    open ghost_counter(id, count);
    open ghost_counter_contrib(id, f, contrib);
    assert [_]ghost_cell<info>(id, ?info);
    switch (info) {
        case info(tokenCell, list):
            assert raw_ghost_list_member_handle<cinfo>(list, ?k, ?cinfo);
            raw_ghost_list_match(list, k);
            pair<int, cinfo> e = pair(k, cinfo);
            switch (cinfo) {
                case cinfo(contribCell, tokenFrac):
		    foreach2_mem(e);
		    open foreach2_mem_results<pair<int, cinfo>, int>(?es0, ?es1, ?cs0, ?c, ?cs1);
		    open contrib(tokenCell)(e, c);
		    if (contrib == 1) {
		        raw_ghost_list_remove(list, k);
		        foreach2_append(es0, es1);
		        forall_append(cs0, cons(c, cs1), nonneg);
		        forall_append(cs0, cs1, nonneg);
		        sum_append(cs0, cons(c, cs1));
		        sum_append(cs0, cs1);
		        nonneg_sum(append(cs0, cs1));
		        ghost_cell_leak(contribCell);
		    } else {
		        ghost_cell_mutate<int>(contribCell, c - 1);
		        close contrib(tokenCell)(e, c - 1);
		        close foreach2(cons(e, es1), contrib(tokenCell), cons(c - 1, cs1));
		        foreach2_append(es0, cons(e, es1));
		        forall_append(cs0, cons(c, cs1), nonneg);
		        forall_append(cs0, cons(c - 1, cs1), nonneg);
		        sum_append(cs0, cons(c, cs1));
		        sum_append(cs0, cons(c - 1, cs1));
		        nonneg_sum(append(cs0, cons(c - 1, cs1)));
		    }
		    close ghost_counter_contrib(id, f, contrib - 1);
		    close ghost_counter(id, count - 1);
            }
    }
}

lemma void ghost_counter_end_contrib()
    requires ghost_counter_contrib(?id, ?f, 0);
    ensures [f]ghost_counter_zero_contrib(id);
{
    open ghost_counter_contrib(id, f, 0);
    close [f]ghost_counter_zero_contrib(id);
}

lemma void ghost_counter_match_zero_contrib()
    requires ghost_counter(?id, ?count) &*& ghost_counter_zero_contrib(id);
    ensures ghost_counter(id, count) &*& ghost_counter_zero_contrib(id) &*& count == 0;
{
    open ghost_counter(id, count);
    open ghost_counter_zero_contrib(id);
    assert [_]ghost_cell<info>(id, ?info);
    switch (info) {
        case info(tokenCell, list):
            assert raw_ghost_list<cinfo>(list, _, ?es);
            open foreach2(es, _, ?cs);
            switch (es) {
                case nil:
                case cons(e, es0):
                    open contrib(tokenCell)(e, head(cs));
                    ghost_cell_fraction_info(tokenCell);
                    assert false;
            }
            close foreach2(nil, contrib(tokenCell), nil);
    }
    close ghost_counter(id, count);
    close ghost_counter_zero_contrib(id);
}

@*/
