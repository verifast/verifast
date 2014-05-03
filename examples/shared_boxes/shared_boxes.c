//@ #include <ghost_cells.gh>
//@ #include <assoclist.gh>
//@ #include <quantifiers.gh>
//@ #include <listex.gh>
//@ #include "../lcset/ghost_lists.gh"
//@ #include "shared_boxes.gh"

/*@

lemma void keys_take<a, b>(int n, list<pair<a, b> > xs)
    requires 0 <= n &*& n <= length(xs);
    ensures keys(take(n, xs)) == take(n, keys(xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n == 0) {
            } else {
                keys_take(n - 1, xs0);
            }
    }
}

lemma void keys_drop<a, b>(int n, list<pair<a, b> > xs)
    requires 0 <= n &*& n <= length(xs);
    ensures keys(drop(n, xs)) == drop(n, keys(xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n == 0) {
            } else {
                keys_drop(n - 1, xs0);
            }
    }
}

lemma void keys_append<a, b>(list<pair<a, b> > xs, list<pair<a, b> > ys)
    requires true;
    ensures keys(append(xs, ys)) == append(keys(xs), keys(ys));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            keys_append(xs0, ys);
    }
}

lemma void mem_remove_nth<t>(t x, int n, list<t> xs)
    requires 0 <= n &*& n < length(xs) &*& mem(x, remove_nth(n, xs)) == true;
    ensures mem(x, xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n == 0) {
            } else {
                if (x0 == x) {
                } else {
                    mem_remove_nth(x, n - 1, xs0);
                }
            }
    }
}

lemma void distinct_remove_nth<t>(int n, list<t> xs)
    requires 0 <= n &*& n < length(xs) &*& distinct(xs) == true;
    ensures distinct(remove_nth(n, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n == 0) {
            } else {
                if (mem(x0, remove_nth(n - 1, xs0))) {
                    mem_remove_nth(x0, n - 1, xs0);
                }
                distinct_remove_nth(n - 1, xs0);
            }
    }
}

fixpoint bool pred_sat2<S,P>(fixpoint(S,int,P,bool) pred_sat, S s, pair<int, P> p) { return pred_sat(s, fst(p), snd(p)); }

predicate pred_chunk(int id;) = [2/3]ghost_cell(id, _);

predicate shared_box<S,A,P>(int id, fixpoint(S,S,A,list<int>,bool) action_sat, fixpoint(S,int,P,bool) pred_sat, S s) =
  is_preds_preserved(_, action_sat, pred_sat) &*& ghost_list(id, ?ps) &*& forall(ps, (pred_sat2)(pred_sat, s)) == true &*& foreachp(keys(ps), pred_chunk) &*& distinct(keys(ps)) == true;

lemma int create_shared_box<S,A,P>(S s)
    requires is_preds_preserved<S,A,P>(?lem, ?action_sat, ?pred_sat);
    ensures shared_box<S,A,P>(result, action_sat, pred_sat, s);
{
    int id = create_ghost_list<pair<int, P> >();
    close foreachp(nil, pred_chunk);
    close shared_box(id, action_sat, pred_sat, s);
    return id;
}

lemma void shared_box_perform_action0<S,A,P>(int id, S s1, A a)
    requires shared_box<S,A,P>(id, ?action_sat, ?pred_sat, ?s0) &*& action_sat(s0, s1, a, nil) == true;
    ensures shared_box(id, action_sat, pred_sat, s1);
{
    open shared_box(_, _, _, _);
    assert is_preds_preserved(?preds_preserved, _, _);
    assert ghost_list(id, ?ps);
    if (!forall(ps, (pred_sat2)(pred_sat, s1))) {
      pair<int, P> p = not_forall(ps, (pred_sat2)(pred_sat, s1));
      forall_elim(ps, (pred_sat2)(pred_sat, s0), p);
      assert p == pair(?pid, ?pp);
      preds_preserved(s0, s1, nil, a, pid, pp);
    }
    close shared_box(id, action_sat, pred_sat, s1);
}

lemma void shared_box_perform_action1<S,A,P>(int id, S s1, A a, int actionHandle)
    requires shared_box<S,A,P>(id, ?action_sat, ?pred_sat, ?s0) &*& action_sat(s0, s1, a, {actionHandle}) == true &*& ghost_cell(actionHandle, ?v);
    ensures shared_box(id, action_sat, pred_sat, s1) &*& ghost_cell(actionHandle, v);
{
    open shared_box(_, _, _, _);
    assert is_preds_preserved(?preds_preserved, _, _);
    assert ghost_list(id, ?ps);
    if (!forall(ps, (pred_sat2)(pred_sat, s1))) {
        pair<int, P> p = not_forall(ps, (pred_sat2)(pred_sat, s1));
        forall_elim(ps, (pred_sat2)(pred_sat, s0), p);
        assert p == pair(?pid, ?pp);
        if (pid == actionHandle) {
            mem_keys(pid, pp, ps);
            foreachp_remove(pid, keys(ps));
            open pred_chunk(pid);
            ghost_cell_fraction_info(pid);
        }
        preds_preserved(s0, s1, {actionHandle}, a, pid, pp);
    }
    close shared_box(id, action_sat, pred_sat, s1);
}

predicate shared_box_pred<P>(int id, int handleId, P p) = ghost_list_member_handle(id, pair(handleId, p));

lemma void shared_box_add_pred<S,A,P>(int id, int handleId, P p)
    requires shared_box(id, ?action_sat, ?pred_sat, ?s) &*& pred_sat(s, handleId, p) == true &*& [2/3]ghost_cell(handleId, _);
    ensures shared_box(id, action_sat, pred_sat, s) &*& shared_box_pred(id, handleId, p);
{
    open shared_box(_, _, _, _);
    assert ghost_list(id, ?ps);
    ghost_list_insert(id, nil, ps, pair(handleId, p));
    close shared_box_pred(id, handleId, p);
    if (mem(handleId, keys(ps))) {
        foreachp_remove(handleId, keys(ps));
        open pred_chunk(handleId);
        ghost_cell_fraction_info(handleId);
    }
    close shared_box(id, action_sat, pred_sat, s);
}

lemma void shared_box_remove_pred<S,A,P>(int id, int handleId)
    requires shared_box(id, ?action_sat, ?pred_sat, ?s) &*& shared_box_pred(id, handleId, ?p);
    ensures shared_box(id, action_sat, pred_sat, s) &*& pred_sat(s, handleId, p) == true &*& [2/3]ghost_cell(handleId, _);
{
    open shared_box(_, _, _, _);
    open shared_box_pred(_, _, _);
    assert ghost_list(id, ?ps);
    ghost_list_member_handle_lemma();
    int n = index_of(pair(handleId, p), ps);
    append_take_drop_n(ps, n);
    mem_nth_index_of(pair(handleId, p), ps);
    drop_n_plus_one(n, ps);
    assert ps == append(take(n, ps), cons(pair(handleId, p), drop(n + 1, ps)));
    ghost_list_remove(id, take(n, ps), drop(n + 1, ps), pair(handleId, p));
    forall_append(take(n, ps), cons(pair(handleId, p), drop(n + 1, ps)), (pred_sat2)(pred_sat, s));
    forall_append(take(n, ps), drop(n + 1, ps), (pred_sat2)(pred_sat, s));
    drop_take_remove_nth(ps, n);
    keys_take(n, ps);
    keys_drop(n, ps);
    drop_take_remove_nth(keys(ps), n);
    drop_n_plus_one(n, keys(ps));
    assert remove_nth(n, keys(ps)) == append(take(n, keys(ps)), drop(n + 1, keys(ps)));
    keys_append(take(n, ps), drop(n, ps));
    keys_append(take(n, ps), drop(n + 1, ps));
    assert remove_nth(n, keys(ps)) == keys(append(take(n, ps), drop(n + 1, ps)));
    foreachp_remove_nth(n);
    distinct_remove_nth(n, keys(ps));
    close shared_box(id, action_sat, pred_sat, s);
}

@*/