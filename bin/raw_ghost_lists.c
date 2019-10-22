//@ #include "ghost_cells.gh"
//@ #include "raw_ghost_lists.gh"

/*@

inductive node_type<t> = final_node | internal_node(t value, int killCell, int next);

predicate leaked_ghost_cell<t>(int id; t value) = [_]ghost_cell(id, value);

lemma void dup_leaked_ghost_cell<t>(int id)
    requires [1/3]leaked_ghost_cell<t>(id, ?value);
    ensures [2/3]leaked_ghost_cell<t>(id, value);
{
    open leaked_ghost_cell(id, value);
    close [2/3]leaked_ghost_cell(id, value);
}

predicate ghost_list_core<t>(int id, int offset; int n, list<pair<int, t> > elements) =
    [1/2]ghost_cell<node_type<t> >(id, ?t) &*&
    switch (t) {
        case final_node: return n == 0 &*& elements == nil &*& [1/2]ghost_cell<node_type<t> >(id, t);
        case internal_node(value, killCell, next): return
            [1/3]leaked_ghost_cell<node_type<t> >(id, t) &*&
            ghost_list_core(next, offset + 1, ?n0, ?elements0) &*& 0 <= n0 &*&
            [1/2]ghost_cell<bool>(killCell, ?dead) &*&
            n == n0 + 1 &*&
            elements == (dead ? elements0 : cons(pair(offset, value), elements0));
    };

lemma void ghost_list_core_fraction_info<t>()
    requires [?f]ghost_list_core<t>(?id, ?offset, ?n, ?elems);
    ensures [f]ghost_list_core<t>(id, offset, n, elems);
{
    open ghost_list_core(id, offset, n, elems);
    ghost_cell_fraction_info<node_type<t> >(id);
}

predicate raw_ghost_list<t>(int id; int n, list<pair<int, t> > elements) =
    ghost_list_core(id, 0, n, elements);

predicate handle_core<t>(int id, int offset, int k; t element) =
    [1/3]leaked_ghost_cell<node_type<t> >(id, ?t) &*&
    switch (t) {
        case final_node: return false &*& element == default_value;
        case internal_node(value, killCell, next): return
            k == offset ?
                [1/2]ghost_cell<bool>(killCell, false) &*&
                element == value
            :
                handle_core<t>(next, offset + 1, k, element);
    };
predicate raw_ghost_list_member_handle<t>(int id, int k; t element) =
    handle_core(id, 0, k, element);

lemma int create_raw_ghost_list<t>()
    requires emp;
    ensures raw_ghost_list<t>(result, 0, nil);
{
    int id = create_ghost_cell<node_type<t> >(final_node);
    close ghost_list_core(id, 0, 0, nil);
    close raw_ghost_list(id, 0, nil);
    return id;
}

lemma void ghost_cell_leaker_helper<t>(int id)
    requires [1/2]ghost_cell<t>(id, ?value);
    ensures leaked_ghost_cell<t>(id, value);
{
    leak [1/2]ghost_cell<t>(id, value);
    close leaked_ghost_cell<t>(id, value);
}

lemma void ghost_list_add_core<t>(int id, int offset, t x)
    requires ghost_list_core<t>(id, offset, ?n, ?xs);
    ensures ghost_list_core<t>(id, offset, n + 1, append(xs, cons(pair(offset + n, x), nil))) &*& handle_core<t>(id, offset, offset + n, x);
{
    open ghost_list_core(id, offset, n, xs);
    assert [_]ghost_cell<node_type<t> >(id, ?t);
    switch (t) {
        case final_node:
            int killCell = create_ghost_cell<bool>(false);
            int finalNode = create_ghost_cell<node_type<t> >(final_node);
            ghost_cell_mutate(id, internal_node(x, killCell, finalNode));
            ghost_cell_leaker_helper<node_type<t> >(id);
            dup_leaked_ghost_cell(id);
            close ghost_list_core<t>(finalNode, offset + 1, n, nil);
            close ghost_list_core<t>(id, offset, n + 1, append(xs, cons(pair(offset + n, x), nil)));
            close handle_core<t>(id, offset, offset + n, x);
            open leaked_ghost_cell(id, _);
        case internal_node(value, killCell, next):
            ghost_list_add_core(next, offset + 1, x);
            dup_leaked_ghost_cell(id);
            close ghost_list_core<t>(id, offset, n + 1, append(xs, cons(pair(offset + n, x), nil)));
            close handle_core<t>(id, offset, offset + n, x);
    }
}

lemma void raw_ghost_list_add<t>(int id, t x)
    requires raw_ghost_list<t>(id, ?n, ?xs);
    ensures raw_ghost_list<t>(id, n + 1, append(xs, cons(pair(n, x), nil))) &*& raw_ghost_list_member_handle<t>(id, n, x);
{
    open raw_ghost_list(id, n, xs);
    ghost_list_add_core(id, 0, x);
    close raw_ghost_list(id, n + 1, append(xs, cons(pair(n, x), nil)));
    close raw_ghost_list_member_handle<t>(id, n, x);
}

lemma void handle_core_fraction_info<t>(int id, int offset, int k)
    requires [?f]handle_core<t>(id, offset, k, ?x);
    ensures [f]handle_core<t>(id, offset, k, x) &*& 0 < f;
{
    open handle_core<t>(id, offset, k, x);
    if (k == offset) {
        assert [_]ghost_cell<bool>(?killCell, _);
        ghost_cell_fraction_info<bool>(killCell);
    } else {
        assert [f]handle_core(?next, offset + 1, k, x);
        handle_core_fraction_info<t>(next, offset + 1, k);
    }
    close [f]handle_core<t>(id, offset, k, x);
}

lemma void ghost_list_match_core<t>(int id, int offset, int k)
    requires [?fl]ghost_list_core<t>(id, offset, ?n, ?xs) &*& [?f]handle_core<t>(id, offset, k, ?x);
    ensures [fl]ghost_list_core<t>(id, offset, n, xs) &*& [f]handle_core<t>(id, offset, k, x) &*& mem(pair(k, x), xs) == true;
{
    open ghost_list_core<t>(id, offset, n, xs);
    ghost_cell_fraction_info<node_type<t> >(id);
    handle_core_fraction_info(id, offset, k);
    open handle_core<t>(id, offset, k, x);
    assert [_]ghost_cell<node_type<t> >(id, ?t);
    switch (t) {
        case final_node:
            open leaked_ghost_cell(id, _);
        case internal_node(value, killCell, next):
            if (offset == k) {
            } else {
                ghost_list_match_core(next, offset + 1, k);
            }
            close [fl]ghost_list_core<t>(id, offset, n, xs);
            close [f]handle_core<t>(id, offset, k, x);
    }
}

lemma void raw_ghost_list_match<t>(int id, int k)
    requires [?fl]raw_ghost_list<t>(id, ?n, ?xs) &*& [?f]raw_ghost_list_member_handle<t>(id, k, ?x);
    ensures [fl]raw_ghost_list<t>(id, n, xs) &*& [f]raw_ghost_list_member_handle<t>(id, k, x) &*& mem(pair(k, x), xs) == true;
{
    open raw_ghost_list(id, n, xs);
    open raw_ghost_list_member_handle(id, k, x);
    ghost_list_match_core(id, 0, k);
    close [fl]raw_ghost_list(id, n, xs);
    close [f]raw_ghost_list_member_handle(id, k, x);
}

lemma void ghost_list_remove_core<t>(int id, int offset, int k)
    requires ghost_list_core<t>(id, offset, ?n, ?xs) &*& handle_core<t>(id, offset, k, ?x);
    ensures ghost_list_core<t>(id, offset, n, remove(pair(k, x), xs));
{
    open ghost_list_core<t>(id, offset, n, xs);
    open handle_core<t>(id, offset, k, x);
    assert [_]ghost_cell<node_type<t> >(id, ?t);
    switch (t) {
        case final_node:
            open leaked_ghost_cell(id, _);
        case internal_node(value, killCell, next):
            if (offset == k) {
                ghost_cell_mutate(killCell, true);
                close ghost_list_core<t>(id, offset, n, remove(pair(k, x), xs));
                ghost_cell_leak(killCell);
                open leaked_ghost_cell(id, _);
            } else {
                ghost_list_remove_core(next, offset + 1, k);
                close ghost_list_core<t>(id, offset, n, remove(pair(k, x), xs));
                open leaked_ghost_cell(id, _);
            }
    }
}

lemma void raw_ghost_list_remove<t>(int id, int k)
    requires raw_ghost_list<t>(id, ?n, ?xs) &*& raw_ghost_list_member_handle<t>(id, k, ?x);
    ensures raw_ghost_list<t>(id, n, remove(pair(k, x), xs));
{
    open raw_ghost_list<t>(id, n, xs);
    open raw_ghost_list_member_handle<t>(id, k, x);
    ghost_list_remove_core<t>(id, 0, k);
    close raw_ghost_list<t>(id, n, remove(pair(k, x), xs));
}

@*/