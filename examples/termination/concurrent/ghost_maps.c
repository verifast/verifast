//@ #include "ghost_cells.gh"
//@ #include "ghost_maps.gh"
//@ #include "listex.gh"

/*@

inductive node_type<t> = final_node | internal_node(t value, int next);

predicate leaked_ghost_cell<t>(int id; t value) = [_]ghost_cell(id, value);

lemma void dup_leaked_ghost_cell<t>(int id)
    requires [1/3]leaked_ghost_cell<t>(id, ?value);
    ensures [2/3]leaked_ghost_cell<t>(id, value);
{
    open leaked_ghost_cell(id, value);
    close [2/3]leaked_ghost_cell(id, value);
}

predicate ghost_list_core<t>(int id; list<t> elements) =
    [1/2]ghost_cell<node_type<t> >(id, ?t) &*&
    switch (t) {
        case final_node: return elements == nil &*& [1/2]ghost_cell<node_type<t> >(id, t);
        case internal_node(value, next): return
            [1/3]leaked_ghost_cell<node_type<t> >(id, t) &*&
            ghost_list_core(next, ?elements0) &*&
            elements == cons(value, elements0);
    };
predicate ghost_map<a, b>(int id; list<pair<a, b> > elements) =
    ghost_list_core(id, elements) &*& distinct(map(fst, elements)) == true;

predicate handle_core<a, b>(int id, a key; b value) =
    [1/3]leaked_ghost_cell<node_type<pair<a, b> > >(id, ?t) &*&
    switch (t) {
        case final_node: return false &*& value == default_value;
        case internal_node(v, next): return
            fst(v) == key ?
                value == snd(v)
            :
                handle_core<a, b>(next, key, value);
    };
predicate ghost_map_entry_handle<a, b>(int id, a key; b value) =
    handle_core(id, key, value);

lemma int create_ghost_map<a, b>()
    requires emp;
    ensures ghost_map<a, b>(result, nil);
{
    int id = create_ghost_cell<node_type<pair<a, b> > >(final_node);
    close ghost_list_core(id, nil);
    close ghost_map<a, b>(id, nil);
    return id;
}

lemma void ghost_cell_leaker_helper<t>(int id)
    requires [1/2]ghost_cell<t>(id, ?value);
    ensures leaked_ghost_cell<t>(id, value);
{
    leak [1/2]ghost_cell<t>(id, value);
    close leaked_ghost_cell<t>(id, value);
}

lemma void ghost_map_add_core<a, b>(int id, a key, b value)
    requires ghost_list_core<pair<a, b> >(id, ?xs) &*& !mem(key, map(fst, xs)) &*& distinct(map(fst, xs)) == true;
    ensures
        ghost_list_core<pair<a, b> >(id, append(xs, {pair(key, value)})) &*& handle_core<a, b>(id, key, value) &*&
        distinct(map(fst, append(xs, {pair(key, value)}))) == true;
{
    open ghost_list_core(id, xs);
    assert [_]ghost_cell<node_type<pair<a, b> > >(id, ?t);
    switch (t) {
        case final_node:
            int finalNode = create_ghost_cell<node_type<pair<a, b> > >(final_node);
            ghost_cell_mutate(id, internal_node(pair(key, value), finalNode));
            ghost_cell_leaker_helper<node_type<pair<a, b> > >(id);
            dup_leaked_ghost_cell(id);
            close ghost_list_core<pair<a, b> >(finalNode, nil);
            close ghost_list_core<pair<a, b> >(id, append(xs, {pair(key, value)}));
            close handle_core<a, b>(id, key, value);
            open leaked_ghost_cell(id, _);
        case internal_node(v, next):
            assert v == pair(?key_, ?value_);
            ghost_map_add_core(next, key, value);
            map_append(fst, xs, {pair(key, value)});
            map_append(fst, tail(xs), {pair(key, value)});
            mem_append(key_, map(fst, tail(xs)), {key});
            assert distinct(map(fst, append(tail(xs), {pair(key, value)}))) == true;
            assert !mem(key_, map(fst, append(tail(xs), {pair(key, value)})));
            assert distinct(map(fst, append(xs, {pair(key, value)}))) == true;
            dup_leaked_ghost_cell(id);
            close ghost_list_core(id, append(xs, cons(pair(key, value), nil)));
            close handle_core(id, key, value);
    }
}

lemma void ghost_map_add<a, b>(int id, a key, b value)
    requires ghost_map<a, b>(id, ?es) &*& !mem(key, map(fst, es));
    ensures ghost_map<a, b>(id, append(es, {pair(key, value)})) &*& [_]ghost_map_entry_handle<a, b>(id, key, value);
{
    open ghost_map(id, es);
    ghost_map_add_core(id, key, value);
    close ghost_map(id, append(es, {pair(key, value)}));
    close ghost_map_entry_handle<a, b>(id, key, value);
    leak ghost_map_entry_handle(id, key, value);
}

lemma void ghost_map_match_core<a, b>(int id, a key)
    requires ghost_list_core<pair<a, b> >(id, ?xs) &*& [_]handle_core<a, b>(id, key, ?value);
    ensures ghost_list_core<pair<a, b> >(id, xs) &*& mem(pair(key, value), xs) == true;
{
    open ghost_list_core<pair<a, b> >(id, xs);
    open handle_core<a, b>(id, key, value);
    assert [_]ghost_cell<node_type<pair<a, b> > >(id, ?t);
    switch (t) {
        case final_node:
            open leaked_ghost_cell(id, _);
        case internal_node(v, next):
            assert v == pair(_, _);
            if (fst(v) == key) {
            } else {
                ghost_map_match_core(next, key);
            }
            close ghost_list_core<pair<a, b> >(id, xs);
            open leaked_ghost_cell(id, _);
    }
}

lemma void ghost_map_match<a, b>(int id, a key)
    requires ghost_map<a, b>(id, ?es) &*& [_]ghost_map_entry_handle<a, b>(id, key, ?value);
    ensures ghost_map<a, b>(id, es) &*& mem(pair(key, value), es) == true;
{
    open ghost_map(id, es);
    open ghost_map_entry_handle(id, key, value);
    ghost_map_match_core(id, key);
    close ghost_map(id, es);
}

lemma b ghost_map_get_entry_handle_core<a, b>(int id, a key)
    requires ghost_list_core<pair<a, b> >(id, ?xs) &*& mem(key, map(fst, xs)) == true;
    ensures ghost_list_core<pair<a, b> >(id, xs) &*& handle_core<a, b>(id, key, result) &*& mem(pair(key, result), xs) == true;
{
    open ghost_list_core(_, _);
    assert [_]ghost_cell<node_type<pair<a, b> > >(id, ?t);
    switch (t) {
        case final_node:
            assert false;
        case internal_node(v, next):
            assert v == pair(_, _);
            b result;
            if (fst(v) == key) {
                result = snd(v);
            } else {
                result = ghost_map_get_entry_handle_core(next, key);
            }
            dup_leaked_ghost_cell(id);
            close ghost_list_core<pair<a, b> >(id, xs);
            close handle_core<a, b>(id, key, result);
            return result;
    }
}

lemma b ghost_map_get_entry_handle<a, b>(int id, a key)
    requires ghost_map<a, b>(id, ?es) &*& mem(key, map(fst, es)) == true;
    ensures ghost_map<a, b>(id, es) &*& [_]ghost_map_entry_handle<a, b>(id, key, result) &*& mem(pair(key, result), es) == true;
{
    open ghost_map(_, _);
    b result = ghost_map_get_entry_handle_core(id, key);
    leak ghost_map_entry_handle(id, key, result);
    return result;
}

lemma void ghost_map_keys_distinct<a, b>(int id)
    requires ghost_map<a, b>(id, ?es);
    ensures ghost_map<a, b>(id, es) &*& distinct(map(fst, es)) == true;
{
    open ghost_map(id, es);
}

@*/