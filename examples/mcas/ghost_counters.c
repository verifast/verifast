//@ #include "ghost_counters.gh"

//@ #include <strong_ghost_lists.gh>
//@ #include <quantifiers.gh>

/*@

fixpoint bool ge(int x, int y) { return x >= y; }

predicate ghost_counter(int id, int count) = strong_ghost_list(id, ?snapshots) &*& forall(snapshots, (ge)(count)) == true;
predicate ghost_counter_snapshot(int id, int snapshot) = strong_ghost_list_member_handle(id, snapshot);

lemma int create_ghost_counter(int count0)
    requires true;
    ensures ghost_counter(result, count0);
{
    int id = create_strong_ghost_list<int>();
    close ghost_counter(id, count0);
    return id;
}

lemma void ghost_counter_add(int delta)
    requires ghost_counter(?id, ?count) &*& 0 <= delta;
    ensures ghost_counter(id, count + delta);
{
    open ghost_counter(id, count);
    assert strong_ghost_list(id, ?snapshots);
    if (!forall(snapshots, (ge)(count + delta))) {
        int snapshot = not_forall(snapshots, (ge)(count + delta));
        forall_elim(snapshots, (ge)(count), snapshot);
        assert false;
    }
    close ghost_counter(id, count + delta);
}

lemma void create_ghost_counter_snapshot(int snapshot)
    requires ghost_counter(?id, ?count) &*& snapshot <= count;
    ensures ghost_counter(id, count) &*& [_]ghost_counter_snapshot(id, snapshot);
{
    open ghost_counter(id, count);
    assert strong_ghost_list(id, ?snapshots);
    strong_ghost_list_insert(id, nil, snapshots, snapshot);
    close ghost_counter(id, count);
    close ghost_counter_snapshot(id, snapshot);
    leak ghost_counter_snapshot(id, snapshot);
}

lemma void match_ghost_counter_snapshot(int snapshot)
    requires ghost_counter(?id, ?count) &*& [_]ghost_counter_snapshot(id, snapshot);
    ensures ghost_counter(id, count) &*& snapshot <= count;
{
    open ghost_counter(id, count);
    open [?f]ghost_counter_snapshot(id, snapshot);
    assert strong_ghost_list(id, ?snapshots);
    strong_ghost_list_member_handle_lemma();
    forall_elim(snapshots, (ge)(count), snapshot);
    close ghost_counter(id, count);
}

@*/