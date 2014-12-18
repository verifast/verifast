//@ #include "levels.gh"
//@ #include "ghost_cells.gh"
//@ #include "ghost_counters.gh"
//@ #include "ghost_lists.gh"
//@ #include "listex.gh"
//@ #include "quantifiers.gh"
//@ #include "obligations.gh"

/*@

fixpoint list<t> flatten<t>(list<list<t> > xss) {
    switch (xss) {
        case nil: return nil;
        case cons(xs, xss0): return append(xs, flatten(xss0));
    }
}

predicate_ctor thread_p(int obligationsId)(pair<list<level>, option<pair<real, level> > > thread;) =
    thread == pair(?obligationSet, ?calling) &*&
    switch (calling) {
        case none: return true;
        case some(p): return p == pair(?frac, ?level) &*& [frac]ghost_list_member_handle(obligationsId, level) &*& level_all_above(obligationSet, level) == true;
    };

predicate n_times(int n, predicate() p) =
    n == 0 ?
        true
    :
        p() &*& n_times(n - 1, p);

lemma_auto void n_times_inv()
    requires n_times(?n, ?p);
    ensures n_times(n, p) &*& 0 <= n;
{
    open n_times(_, _);
    if (n != 0)
        n_times_inv();
    close n_times(n, p);
}

fixpoint bool is_thread_not_calling(pair<list<level>, option<pair<real, level> > > thread) { return snd(thread) == none; }

predicate obligation_scope(int id, predicate() p) =
    [_]ghost_cell(id, pair(?threadsId, pair(?obligationsId, ?joineesId))) &*&
    ghost_list<pair<list<level>, option<pair<real, level> > > >(threadsId, ?threads) &*&
    ghost_list<level>(obligationsId, flatten(map(fst, threads))) &*&
    ghost_counter(joineesId, ?joineeCount) &*&
    foreach(threads, thread_p(obligationsId)) &*&
    joineeCount == length(threads) - 1 &*&
    n_times(count(threads, is_thread_not_calling) - 1, p);

predicate obligation_scope_joinee(int scope) =
    [_]ghost_cell<pair<int, pair<int, int> > >(scope, pair(?threadsId, pair(?obligationsId, ?joineesId))) &*&
    ghost_counter_ticket(joineesId);

predicate obligation(int scope, level level;) =
    [_]ghost_cell<pair<int, pair<int, int> > >(scope, pair(?threadsId, pair(?obligationsId, ?joineesId))) &*&
    ghost_list_member_handle(obligationsId, level);

predicate obligation_set(int scope, list<level> levels) =
    [_]ghost_cell<pair<int, pair<int, int> > >(scope, pair(?threadsId, pair(?obligationsId, ?joineesId))) &*&
    ghost_list_member_handle<pair<list<level>, option<pair<real, level> > > >(threadsId, pair(levels, none));

predicate obligation_set_calling(int scope, list<level> levels, real frac, level level) =
    [_]ghost_cell<pair<int, pair<int, int> > >(scope, pair(?threadsId, pair(?obligationsId, ?joineesId))) &*&
    ghost_list_member_handle(threadsId, pair(levels, some(pair(frac, level))));

lemma int create_obligation_scope(predicate() p)
    requires true;
    ensures obligation_scope(result, p) &*& obligation_set(result, nil);
{
    int threadsId = create_ghost_list<pair<list<level>, option<pair<real, level> > > >();
    int obligationsId = create_ghost_list<level>();
    int joineesId = create_ghost_counter();
    int id = create_ghost_cell(pair(threadsId, pair(obligationsId, joineesId)));
    leak ghost_cell(id, _);
    ghost_list_insert(threadsId, nil, nil, pair(nil, none));
    close foreach(nil, thread_p(obligationsId));
    close thread_p(obligationsId)(pair(nil, none));
    close foreach({pair(nil, none)}, thread_p(obligationsId));
    close n_times(0, p);
    close obligation_scope(id, p);
    close obligation_set(id, nil);
    return id;
}

lemma void join_obligation_scope(int scope)
    requires obligation_scope(scope, ?p) &*& p();
    ensures obligation_scope(scope, p) &*& obligation_set(scope, nil) &*& obligation_scope_joinee(scope);
{
    open obligation_scope(scope, p);
    assert [_]ghost_cell(scope, pair(?threadsId, pair(?obligationsId, ?joineesId)));
    assert ghost_list<pair<list<level>, option<pair<real, level> > > >(threadsId, ?threads);
    ghost_list_insert(threadsId, nil, threads, pair(nil, none));
    close thread_p(obligationsId)(pair(nil, none));
    close foreach(cons(pair(nil, none), threads), thread_p(obligationsId));
    close n_times(count(threads, is_thread_not_calling), p);
    assert ghost_counter(joineesId, _);
    create_ghost_counter_ticket(joineesId);
    close obligation_scope(scope, p);
    close obligation_set(scope, nil);
    close obligation_scope_joinee(scope);
}

#define THREAD pair<list<level>, option<pair<real, level> > >

lemma pair<list<THREAD>, list<THREAD> > remove_thread(list<THREAD> threads, int obligationsId)
    requires foreach(threads, thread_p(obligationsId)) &*& mem(pair(nil, none), threads) == true;
    ensures
        result == pair(?ts1, ?ts2) &*& threads == append(ts1, cons(pair(nil, none), ts2)) &*&
        flatten(map(fst, threads)) == flatten(map(fst, append(ts1, ts2))) &*&
        count(threads, is_thread_not_calling) == count(append(ts1, ts2), is_thread_not_calling) + 1 &*&
        foreach(append(ts1, ts2), thread_p(obligationsId));
{
    open foreach(_, _);
    assert threads == cons(?t, ?ts0);
    assert t == pair(?t_obs, ?t_calling);
    option<pair<real, level> > t_calling_ = t_calling;
    switch (t_calling_) { case none: case some(info): }
    if (t == pair(nil, none)) {
        open thread_p(obligationsId)(t);
        if (t_calling == none) {
            assert is_thread_not_calling(pair(nil, none)) == true;
            assert count(threads, is_thread_not_calling) == count(ts0, is_thread_not_calling) + 1;
        }
        return pair(nil, ts0);
    } else {
        pair<list<THREAD>, list<THREAD> > p = remove_thread(ts0, obligationsId);
        assert p == pair(?ts10, ?ts2);
        close foreach(cons(t, append(ts10, ts2)), thread_p(obligationsId));
        return pair(cons(t, ts10), ts2);
    }
}

fixpoint bool level_above_or_eq(level level1, level level2) { return level1 == level2 || level_above(level1, level2); }

fixpoint bool is_thread_calling_below(option<level> level, THREAD thread) {
    switch (level) {
        case none: return true;
        case some(level_): return exists(fst(thread), (level_above_or_eq)(level_));
    }
}

lemma list<t> mem_flatten<t>(t x, list<list<t> > xss)
    requires mem(x, flatten(xss)) == true;
    ensures mem(result, xss) && mem(x, result);
{
    switch (xss) {
        case nil:
        case cons(xs, xss0):
            if (mem(x, xs)) {
                return xs;
            } else {
                return mem_flatten(x, xss0);
            }
    }
}

lemma a mem_map_mem<a, b>(b y, fixpoint(a, b) f, list<a> xs)
    requires mem(y, map(f, xs)) == true;
    ensures mem(result, xs) && f(result) == y;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (f(x) == y) {
                return x;
            } else {
                return mem_map_mem(y, f, xs0);
            }
    }
}

lemma void mem_exists<t>(t x, list<t> xs, fixpoint(t, bool) p)
    requires mem(x, xs) && p(x);
    ensures exists(xs, p) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
            } else {
                mem_exists(x, xs0, p);
            }
    }
}

lemma THREAD thread_calling_below_step(list<THREAD> threads, int obligationsId, list<level> obs, real frac, level level, list<THREAD> ts)
    requires
        foreach(ts, thread_p(obligationsId)) &*&
        ghost_list<level>(obligationsId, flatten(map(fst, threads))) &*&
        mem(pair(obs, some(pair(frac, level))), ts) == true;
    ensures
        ghost_list<level>(obligationsId, flatten(map(fst, threads))) &*&
        foreach(ts, thread_p(obligationsId)) &*&
        level_all_above(obs, level) &&
        mem(result, threads) && is_thread_calling_below(some(level), result);
{
    open foreach(ts, _);
    assert ts == cons(?t, ?ts0);
    if (t == pair(obs, some(pair(frac, level)))) {
        open thread_p(obligationsId)(_);
        ghost_list_match();
        list<level> t1_obs = mem_flatten(level, map(fst, threads));
        THREAD t1 = mem_map_mem(t1_obs, fst, threads);
        mem_exists(level, t1_obs, (level_above_or_eq)(level));
        close thread_p(obligationsId)(t);
        close foreach(ts, thread_p(obligationsId));
        return t1;
    } else {
        THREAD result = thread_calling_below_step(threads, obligationsId, obs, frac, level, ts0);
        close foreach(ts, thread_p(obligationsId));
        return result;
    }
}

fixpoint bool implies_at<t>(fixpoint(t, bool) p1, fixpoint(t, bool) p2, t x) { return !p1(x) || p2(x); }

lemma void implies_count_le<t>(list<t> xs, fixpoint(t, bool) p1, fixpoint(t, bool) p2)
    requires [_]is_forall_t<t>(?forall_t) &*& forall_t((implies_at)(p2, p1)) == true;
    ensures count(xs, p2) <= count(xs, p1);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            forall_t_elim(forall_t, (implies_at)(p2, p1), x0);
            implies_count_le(xs0, p1, p2);
    }
}

lemma void mem_count_decreases<t>(t x, list<t> xs, fixpoint(t, bool) p1, fixpoint(t, bool) p2)
    requires [_]is_forall_t<t>(?forall_t) &*& mem(x, xs) && p1(x) && !p2(x) && forall_t((implies_at)(p2, p1));
    ensures count(xs, p2) < count(xs, p1);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                implies_count_le(xs0, p1, p2);
            } else {
                forall_t_elim(forall_t, (implies_at)(p2, p1), x0);
                mem_count_decreases(x, xs0, p1, p2);
            }
    }
}

lemma t exists_get_witness<t>(list<t> xs, fixpoint(t, bool) p)
    requires exists(xs, p) == true;
    ensures mem(result, xs) && p(result);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (p(x0))
                return x0;
            else
                return exists_get_witness(xs0, p);
    }
}

lemma void one_thread_not_calling(list<THREAD> threads, int obligationsId)
    requires
        ghost_list<level>(obligationsId, flatten(map(fst, threads))) &*&
        foreach(threads, thread_p(obligationsId)) &*&
        threads != nil;
    ensures
        ghost_list<level>(obligationsId, flatten(map(fst, threads))) &*&
        foreach(threads, thread_p(obligationsId)) &*&
        count(threads, is_thread_not_calling) > 0;
{
    assert threads == cons(?t, ?ts0);
    option<level> level = none;
    
    for (;;)
        invariant
            ghost_list<level>(obligationsId, flatten(map(fst, threads))) &*&
            foreach(threads, thread_p(obligationsId)) &*&
            mem(t, threads) && is_thread_calling_below(level, t);
        decreases count(threads, (is_thread_calling_below)(level));
    {
        assert t == pair(?obs, ?calling);
        if (calling == none) {
            if (count(threads, is_thread_not_calling) == 0) {
                count_zero_mem(threads, is_thread_not_calling, t);
                assert false;
            }
            count_nonnegative(threads, is_thread_not_calling);
            return;
        }
        assert calling == some(pair(?frac, ?level1));
        THREAD t1 = thread_calling_below_step(threads, obligationsId, obs, frac, level1, threads);
        fixpoint(fixpoint(THREAD, bool), bool) forall_THREAD = get_forall_t<THREAD>();
        if (exists(obs, (level_above_or_eq)(level1))) {
            level ob = exists_get_witness(obs, (level_above_or_eq)(level1));
            assert level_all_above(obs, level1) == true;
            forall_elim(obs, (level_below)(level1), ob);
            if (ob == level1) {
                level_below_antireflexive(ob);
                assert false;
            } else {
                level_below_transitive(level1, ob, level1);
                level_below_antireflexive(level1);
                assert false;
            }
        }
        assert !exists(obs, (level_above_or_eq)(level1));
        assert !is_thread_calling_below(some(level1), t);
        if (!forall_THREAD((implies_at)((is_thread_calling_below)(some(level1)), (is_thread_calling_below)(level)))) {
            THREAD t_ = not_forall_t(forall_THREAD, (implies_at)((is_thread_calling_below)(some(level1)), (is_thread_calling_below)(level)));
            assert is_thread_calling_below(some(level1), t_) && !is_thread_calling_below(level, t_);
            assert level == some(?level_);
            assert exists(obs, (level_above_or_eq)(level_)) == true;
            level ob = exists_get_witness(obs, (level_above_or_eq)(level_));
            forall_elim(obs, (level_below)(level1), ob);
            if (!level_below(level1, level_)) {
                if (ob != level_)
                    level_below_transitive(level1, ob, level_);
                assert false;
            }
            assert level_below(level1, level_) == true;
            assert t_ == pair(?t__obs, _);
            level ob_ = exists_get_witness(t__obs, (level_above_or_eq)(level1));
            if (!level_above_or_eq(level_, ob_)) {
                if (ob_ != level1)
                    level_below_transitive(ob_, level1, level_);
                assert false;
            }
            mem_exists(ob_, t__obs, (level_above_or_eq)(level_));
            assert false;
        }
        mem_count_decreases(t, threads, (is_thread_calling_below)(level), (is_thread_calling_below)(some(level1)));
        level = some(level1);
        t = t1;
        count_nonnegative(threads, (is_thread_calling_below)(some(level1)));
    }
}

lemma void flatten_append<t>(list<list<t> > xss1, list<list<t> > xss2)
    requires true;
    ensures flatten(append(xss1, xss2)) == append(flatten(xss1), flatten(xss2));
{
    switch (xss1) {
        case nil:
        case cons(xs, xss10):
            flatten_append(xss10, xss2);
            append_assoc(xs, flatten(xss10), flatten(xss2));
    }
}

lemma void leave_obligation_scope(int scope)
    requires obligation_scope(scope, ?p) &*& obligation_set(scope, nil) &*& obligation_scope_joinee(scope);
    ensures obligation_scope(scope, p) &*& p();
{
    open obligation_scope(scope, p);
    open obligation_set(scope, nil);
    open obligation_scope_joinee(scope);
    assert [_]ghost_cell(scope, pair(?threadsId, pair(?obligationsId, ?joineesId)));
    ghost_list_match();
    assert ghost_list<THREAD>(threadsId, ?ts);
    pair<list<THREAD>, list<THREAD> > ts1_ts2 = remove_thread(ts, obligationsId);
    assert ts1_ts2 == pair(?ts1, ?ts2);
    ghost_list_remove(threadsId, ts1, ts2, pair(nil, none));
    count_nonnegative(append(ts1, ts2), is_thread_not_calling);    
    assert count(ts, is_thread_not_calling) > 0;
    ghost_counter_destroy_ticket(joineesId);
    assert length(ts) > 1;
    assert length(append(ts1, ts2)) > 0;
    one_thread_not_calling(append(ts1, ts2), obligationsId);
    open n_times(_, _);
    flatten_append(map(fst, ts1), cons(nil, map(fst, ts2)));
    flatten_append(map(fst, ts1), map(fst, ts2));
    map_append(fst, ts1, cons(pair(nil, none), ts2));
    map_append(fst, ts1, ts2);
    assert flatten(map(fst, append(ts1, ts2))) == flatten(map(fst, append(ts1, cons(pair(nil, none), ts2))));
    close obligation_scope(scope, p);
}

lemma pair<list<THREAD>, list<THREAD> > create_obligation_helper(list<THREAD> threads, int obligationsId, list<level> obs, level ob)
    requires
        foreach(threads, thread_p(obligationsId)) &*& mem(pair(obs, none), threads) == true;
    ensures
        result == pair(?ts1, ?ts2) &*& threads == append(ts1, cons(pair(obs, none), ts2)) &*&
        foreach(append(ts1, cons(pair(cons(ob, obs), none), ts2)), thread_p(obligationsId)) &*&
        count(append(ts1, cons(pair(cons(ob, obs), none), ts2)), is_thread_not_calling) == count(threads, is_thread_not_calling);
{
    open foreach(threads, thread_p(obligationsId));
    assert threads == cons(?t, ?ts0);
    list<THREAD> ts1;
    list<THREAD> ts2;
    if (t == pair(obs, none)) {
        open thread_p(obligationsId)(t);
        close thread_p(obligationsId)(pair(cons(ob, obs), none));
        ts1 = nil;
        ts2 = ts0;
    } else {
        pair<list<THREAD>, list<THREAD> > result_ = create_obligation_helper(ts0, obligationsId, obs, ob);
        assert result_ == pair(?ts10, ?ts2_);
        ts1 = cons(t, ts10);
        ts2 = ts2_;
    }
    close foreach(append(ts1, cons(pair(cons(ob, obs), none), ts2)), thread_p(obligationsId));
    return pair(ts1, ts2);
}

lemma void create_obligation(level level)
    requires obligation_scope(?scope, ?p) &*& obligation_set(scope, ?obligations);
    ensures obligation_scope(scope, p) &*& obligation_set(scope, cons(level, obligations)) &*& obligation(scope, level);
{
    open obligation_scope(scope, p);
    assert [_]ghost_cell(scope, pair(?threadsId, pair(?obligationsId, ?joineesId)));
    open obligation_set(scope, obligations);
    ghost_list_match();
    assert ghost_list<THREAD>(threadsId, ?threads);
    pair<list<THREAD>, list<THREAD> > ts1_ts2 = create_obligation_helper(threads, obligationsId, obligations, level);
    assert ts1_ts2 == pair(?ts1, ?ts2);
    ghost_list_remove(threadsId, ts1, ts2, pair(obligations, none));
    ghost_list_insert(threadsId, ts1, ts2, pair(cons(level, obligations), none));
    map_append(fst, ts1, cons(pair(obligations, none), ts2));
    flatten_append(map(fst, ts1), map(fst, cons(pair(obligations, none), ts2)));
    ghost_list_insert(obligationsId, flatten(map(fst, ts1)), flatten(map(fst, cons(pair(obligations, none), ts2))), level);
    map_append(fst, ts1, cons(pair(cons(level, obligations), none), ts2));
    flatten_append(map(fst, ts1), map(fst, cons(pair(cons(level, obligations), none), ts2)));
    close obligation_scope(scope, p);
    close obligation_set(scope, cons(level, obligations));
    close obligation(scope, level);
}

lemma pair<list<THREAD>, list<THREAD> > call_obligation_helper(list<THREAD> threads, int obligationsId, list<level> obs, real frac, level ob)
    requires
        foreach(threads, thread_p(obligationsId)) &*& mem(pair(obs, none), threads) == true &*&
        [frac]ghost_list_member_handle(obligationsId, ob) &*& level_all_above(obs, ob) == true;
    ensures
        result == pair(?ts1, ?ts2) &*& threads == append(ts1, cons(pair(obs, none), ts2)) &*&
        foreach(append(ts1, cons(pair(obs, some(pair(frac, ob))), ts2)), thread_p(obligationsId)) &*&
        count(append(ts1, cons(pair(obs, some(pair(frac, ob))), ts2)), is_thread_not_calling) == count(threads, is_thread_not_calling) - 1;
{
    open foreach(threads, thread_p(obligationsId));
    assert threads == cons(?t, ?ts0);
    list<THREAD> ts1;
    list<THREAD> ts2;
    if (t == pair(obs, none)) {
        open thread_p(obligationsId)(t);
        close thread_p(obligationsId)(pair(obs, some(pair(frac, ob))));
        ts1 = nil;
        ts2 = ts0;
    } else {
        pair<list<THREAD>, list<THREAD> > result_ = call_obligation_helper(ts0, obligationsId, obs, frac, ob);
        assert result_ == pair(?ts10, ?ts2_);
        ts1 = cons(t, ts10);
        ts2 = ts2_;
    }
    close foreach(append(ts1, cons(pair(obs, some(pair(frac, ob))), ts2)), thread_p(obligationsId));
    return pair(ts1, ts2);
}

lemma void call_obligation()
    requires obligation_scope(?scope, ?p) &*& obligation_set(scope, ?obligations) &*& [?f]obligation(scope, ?level) &*& level_all_above(obligations, level) == true;
    ensures obligation_scope(scope, p) &*& obligation_set_calling(scope, obligations, f, level) &*& p();
{
    open obligation_scope(scope, p);
    assert [_]ghost_cell(scope, pair(?threadsId, pair(?obligationsId, ?joineesId)));
    open obligation_set(scope, obligations);
    open obligation(scope, level);
    ghost_list_match();
    assert ghost_list<THREAD>(threadsId, ?threads);
    pair<list<THREAD>, list<THREAD> > ts1_ts2 = call_obligation_helper(threads, obligationsId, obligations, f, level);
    assert ts1_ts2 == pair(?ts1, ?ts2);
    ghost_list_remove(threadsId, ts1, ts2, pair(obligations, none));
    ghost_list_insert(threadsId, ts1, ts2, pair(obligations, some(pair(f, level))));
    map_append(fst, ts1, cons(pair(obligations, none), ts2));
    flatten_append(map(fst, ts1), map(fst, cons(pair(obligations, none), ts2)));
    map_append(fst, ts1, cons(pair(obligations, some(pair(f, level))), ts2));
    flatten_append(map(fst, ts1), map(fst, cons(pair(obligations, some(pair(f, level))), ts2)));
    assert length(append(ts1, cons(pair(obligations, some(pair(f, level))), ts2))) > 0;
    one_thread_not_calling(append(ts1, cons(pair(obligations, some(pair(f, level))), ts2)), obligationsId);
    open n_times(_, _);
    close obligation_scope(scope, p);
    close obligation_set_calling(scope, obligations, f, level);
}

lemma pair<list<THREAD>, list<THREAD> > return_obligation_helper(list<THREAD> threads, int obligationsId, list<level> obs, real frac, level ob)
    requires
        foreach(threads, thread_p(obligationsId)) &*& mem(pair(obs, some(pair(frac, ob))), threads) == true;
    ensures
        result == pair(?ts1, ?ts2) &*& threads == append(ts1, cons(pair(obs, some(pair(frac, ob))), ts2)) &*&
        foreach(append(ts1, cons(pair(obs, none), ts2)), thread_p(obligationsId)) &*&
        [frac]ghost_list_member_handle(obligationsId, ob) &*&
        count(append(ts1, cons(pair(obs, none), ts2)), is_thread_not_calling) == count(threads, is_thread_not_calling) + 1;
{
    open foreach(threads, thread_p(obligationsId));
    assert threads == cons(?t, ?ts0);
    list<THREAD> ts1;
    list<THREAD> ts2;
    if (t == pair(obs, some(pair(frac, ob)))) {
        open thread_p(obligationsId)(t);
        close thread_p(obligationsId)(pair(obs, none));
        ts1 = nil;
        ts2 = ts0;
    } else {
        pair<list<THREAD>, list<THREAD> > result_ = return_obligation_helper(ts0, obligationsId, obs, frac, ob);
        assert result_ == pair(?ts10, ?ts2_);
        ts1 = cons(t, ts10);
        ts2 = ts2_;
    }
    close foreach(append(ts1, cons(pair(obs, none), ts2)), thread_p(obligationsId));
    return pair(ts1, ts2);
}

lemma void return_obligation()
    requires obligation_scope(?scope, ?p) &*& obligation_set_calling(scope, ?obligations, ?f, ?level) &*& p();
    ensures obligation_scope(scope, p) &*& obligation_set(scope, obligations) &*& [f]obligation(scope, level);
{
    open obligation_scope(scope, p);
    assert [_]ghost_cell(scope, pair(?threadsId, pair(?obligationsId, ?joineesId)));
    open obligation_set_calling(scope, obligations, f, level);
    ghost_list_match();
    assert ghost_list<THREAD>(threadsId, ?threads);
    pair<list<THREAD>, list<THREAD> > ts1_ts2 = return_obligation_helper(threads, obligationsId, obligations, f, level);
    assert ts1_ts2 == pair(?ts1, ?ts2);
    ghost_list_remove(threadsId, ts1, ts2, pair(obligations, some(pair(f, level))));
    ghost_list_insert(threadsId, ts1, ts2, pair(obligations, none));
    map_append(fst, ts1, cons(pair(obligations, none), ts2));
    flatten_append(map(fst, ts1), map(fst, cons(pair(obligations, none), ts2)));
    map_append(fst, ts1, cons(pair(obligations, some(pair(f, level))), ts2));
    flatten_append(map(fst, ts1), map(fst, cons(pair(obligations, some(pair(f, level))), ts2)));
    list<THREAD> ts_ = append(ts1, cons(pair(obligations, none), ts2));
    assert length(ts_) > 0;
    close n_times(count(ts_, is_thread_not_calling) - 1, p);
    close obligation_scope(scope, p);
    close obligation_set(scope, obligations);
    close [f]obligation(scope, level);    
}

lemma pair<list<THREAD>, list<THREAD> > destroy_obligation_helper(list<THREAD> threads, int obligationsId, list<level> obs, level ob)
    requires
        foreach(threads, thread_p(obligationsId)) &*& mem(pair(obs, none), threads) == true &*& mem(ob, obs) == true;
    ensures
        result == pair(?ts1, ?ts2) &*& threads == append(ts1, cons(pair(obs, none), ts2)) &*&
        foreach(append(ts1, cons(pair(remove(ob, obs), none), ts2)), thread_p(obligationsId)) &*&
        count(append(ts1, cons(pair(remove(ob, obs), none), ts2)), is_thread_not_calling) == count(threads, is_thread_not_calling);
{
    open foreach(threads, thread_p(obligationsId));
    assert threads == cons(?t, ?ts0);
    list<THREAD> ts1;
    list<THREAD> ts2;
    if (t == pair(obs, none)) {
        open thread_p(obligationsId)(t);
        close thread_p(obligationsId)(pair(remove(ob, obs), none));
        ts1 = nil;
        ts2 = ts0;
    } else {
        pair<list<THREAD>, list<THREAD> > result_ = destroy_obligation_helper(ts0, obligationsId, obs, ob);
        assert result_ == pair(?ts10, ?ts2_);
        ts1 = cons(t, ts10);
        ts2 = ts2_;
    }
    close foreach(append(ts1, cons(pair(remove(ob, obs), none), ts2)), thread_p(obligationsId));
    return pair(ts1, ts2);
}

lemma void destroy_obligation()
    requires obligation_scope(?scope, ?p) &*& obligation_set(scope, ?obligations) &*& obligation(scope, ?level) &*& mem(level, obligations) == true;
    ensures obligation_scope(scope, p) &*& obligation_set(scope, remove(level, obligations));
{
    open obligation_scope(scope, p);
    assert [_]ghost_cell(scope, pair(?threadsId, pair(?obligationsId, ?joineesId)));
    open obligation_set(scope, obligations);
    open obligation(scope, level);
    ghost_list_match();
    assert ghost_list<THREAD>(threadsId, ?threads);
    pair<list<THREAD>, list<THREAD> > ts1_ts2 = destroy_obligation_helper(threads, obligationsId, obligations, level);
    assert ts1_ts2 == pair(?ts1, ?ts2);
    ghost_list_remove(threadsId, ts1, ts2, pair(obligations, none));
    ghost_list_insert(threadsId, ts1, ts2, pair(remove(level, obligations), none));
    map_append(fst, ts1, cons(pair(obligations, none), ts2));
    flatten_append(map(fst, ts1), map(fst, cons(pair(obligations, none), ts2)));
    mem_remove_eq_append(level, obligations);
    open exists(pair(?obs1, ?obs2));
    append_assoc(obs1, cons(level, obs2), flatten(map(fst, ts2)));
    append_assoc(flatten(map(fst, ts1)), obs1, append(cons(level, obs2), flatten(map(fst, ts2))));
    ghost_list_remove(obligationsId, append(flatten(map(fst, ts1)), obs1), append(obs2, flatten(map(fst, ts2))), level);
    append_assoc(flatten(map(fst, ts1)), obs1, append(obs2, flatten(map(fst, ts2))));
    append_assoc(obs1, obs2, flatten(map(fst, ts2)));
    map_append(fst, ts1, cons(pair(remove(level, obligations), none), ts2));
    flatten_append(map(fst, ts1), map(fst, cons(pair(remove(level, obligations), none), ts2)));
    close obligation_scope(scope, p);
    close obligation_set(scope, remove(level, obligations));
}

@*/
