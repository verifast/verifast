//@ #include <quantifiers.gh>
//@ #include <ghost_cells.gh>
//@ #include <strong_ghost_lists.gh>
//@ #include "ghost_cells_ex.gh"

/*@

predicate ghost_cell3(int id; int v1, int v2, int v3) = ghost_cell(id, pair(?v1_, pair(?v2_, ?v3_))) &*& v1 == v1_ &*& v2 == v2_ &*& v3 == v3_;

lemma int create_ghost_cell3(int v1, int v2, int v3)
    requires true;
    ensures ghost_cell3(result, v1, v2, v3);
{
    return create_ghost_cell(pair(v1, pair(v2, v3)));
}



inductive ghost_cell6_value = ghost_cell6_value(int v1, int v2, int v3, void *v4, void *v5, any v6);

predicate ghost_cell6(int id; int v1, int v2, int v3, void *v4, void *v5, any v6) = ghost_cell(id, ghost_cell6_value(v1, v2, v3, v4, v5, ?v6_)) &*& v6 == v6_;

lemma int create_ghost_cell6(int v1, int v2, int v3, void *v4, void *v5, any v6)
    requires true;
    ensures ghost_cell6(result, v1, v2, v3, v4, v5, v6);
{
    int id = create_ghost_cell(ghost_cell6_value(v1, v2, v3, v4, v5, v6));
    return id;
}

lemma void ghost_cell6_update(int id, int v1, int v2, int v3, void *v4, void *v5, any v6)
    requires ghost_cell6(id, _, _, _, _, _, _);
    ensures ghost_cell6(id, v1, v2, v3, v4, v5, v6);
{
    ghost_cell_mutate(id, ghost_cell6_value(v1, v2, v3, v4, v5, v6));
}



fixpoint bool eq<t>(t x, t y) { return x == y; }

predicate counted_ghost_cell<t>(int id; t value, int count) =
    [_]ghost_cell(id, pair(?valueId, ?listId)) &*&
    ghost_cell(valueId, value) &*&
    strong_ghost_list(listId, ?elems) &*& forall(elems, (eq)(value)) == true &*& count == length(elems);

predicate counted_ghost_cell_ticket<t>(int id, t value) =
    [_]ghost_cell<pair<int, int> >(id, pair(?valueId, ?listId)) &*&
    strong_ghost_list_member_handle(listId, value);

lemma int create_counted_ghost_cell<t>(t value)
    requires true;
    ensures counted_ghost_cell<t>(result, value, 0);
{
    int valueId = create_ghost_cell(value);
    int listId = create_strong_ghost_list();
    int id = create_ghost_cell(pair(valueId, listId));
    leak ghost_cell(id, _);
    return id;
}

lemma void create_counted_ghost_cell_ticket<t>(int id)
    requires counted_ghost_cell<t>(id, ?value, ?count);
    ensures counted_ghost_cell<t>(id, value, count + 1) &*& counted_ghost_cell_ticket(id, value);
{
    open counted_ghost_cell(id, value, count);
    assert [_]ghost_cell(id, pair(?valueId, ?listId));
    assert strong_ghost_list(listId, ?elems);
    strong_ghost_list_insert(listId, nil, elems, value);
    close counted_ghost_cell_ticket(id, value);
}

lemma void counted_ghost_cell_dispose_ticket<t>(int id)
    requires counted_ghost_cell<t>(id, ?value, ?count) &*& counted_ghost_cell_ticket<t>(id, ?value0);
    ensures counted_ghost_cell<t>(id, value, count - 1) &*& value0 == value;
{
    open counted_ghost_cell(id, value, count);
    open counted_ghost_cell_ticket(id, value0);
    assert [_]ghost_cell(id, pair(?valueId, ?listId));
    assert strong_ghost_list(listId, ?elems);
    strong_ghost_list_member_handle_lemma();
    forall_elim(elems, (eq)(value), value0);
    assert elems == cons(_, _);
    strong_ghost_list_remove(listId, nil, tail(elems), value0);
}

lemma void counted_ghost_cell_match_ticket<t>(int id)
    requires counted_ghost_cell<t>(id, ?value, ?count) &*& counted_ghost_cell_ticket<t>(id, ?value0);
    ensures counted_ghost_cell<t>(id, value, count) &*& counted_ghost_cell_ticket<t>(id, value) &*& value0 == value;
{
    open counted_ghost_cell(id, value, count);
    open counted_ghost_cell_ticket(id, value0);
    assert [_]ghost_cell(id, pair(?valueId, ?listId));
    assert strong_ghost_list(listId, ?elems);
    strong_ghost_list_member_handle_lemma();
    forall_elim(elems, (eq)(value), value0);
    close counted_ghost_cell_ticket(id, value);
}

lemma void counted_ghost_cell_update<t>(int id, t x)
    requires counted_ghost_cell<t>(id, _, 0);
    ensures counted_ghost_cell<t>(id, x, 0);
{
    open counted_ghost_cell(id, _, 0);
    assert [_]ghost_cell(id, pair(?valueId, ?listId));
    assert strong_ghost_list(listId, ?elems);
    switch (elems) { case nil: case cons(h, t): }
    ghost_cell_mutate(valueId, x);
    close counted_ghost_cell(id, x, 0);
}

@*/
