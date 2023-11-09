// tab_size:4

// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

/*@

box_class growing_list0(list<int> xs) {
  invariant true;
  action noop();
    requires true;
    ensures xs == old_xs;
  action add(int elem);
    requires true;
    ensures xs == append(old_xs, {elem});
  handle_predicate has_at0(int k, int x) {
    invariant 0 <= k && k < length(xs) && nth(k, xs) == x;
    preserved_by noop() {}
    preserved_by add(elem) {
      nth_append(old_xs, {elem}, k);
    }
  }
}

predicate ghost_cells<t>(list<int> ids; list<t> values) =
    switch (ids) {
        case nil: return values == nil;
        case cons(id, ids0): return [_]ghost_cell<t>(id, ?value) &*& ghost_cells(ids0, ?values0) &*& values == cons(value, values0);
    };

lemma int ghost_cells_add<t>(t value)
    requires ghost_cells<t>(?ids, ?values);
    ensures ghost_cells<t>(append(ids, {result}), append(values, {value}));
{
    open ghost_cells(ids, values);
    int result;
    if (ids == nil) {
        result = create_ghost_cell(value);
        leak ghost_cell(result, value);
    } else {
        result = ghost_cells_add(value);
    }
    close ghost_cells(append(ids, {result}), append(values, {value}));
    return result;
}

lemma void ghost_cells_lookup<t>(int index)
    requires ghost_cells<t>(?ids, ?values) &*& 0 <= index &*& index < length(ids);
    ensures ghost_cells<t>(ids, values) &*& [_]ghost_cell<t>(nth(index, ids), nth(index, values));
{
    open ghost_cells(ids, values);
    if (index == 0) {
    } else {
        ghost_cells_lookup(index - 1);
    }
    close ghost_cells<t>(ids, values);
}

lemma void ghost_cells_match<t>(int index)
    requires ghost_cells<t>(?ids, ?values) &*& 0 <= index &*& index < length(ids) &*& [_]ghost_cell<t>(nth(index, ids), ?value);
    ensures ghost_cells<t>(ids, values) &*& nth(index, values) == value;
{
    open ghost_cells(ids, values);
    if (index == 0) {
        merge_fractions ghost_cell(nth(index, ids), _);
    } else {
        ghost_cells_match(index - 1);
    }
    close ghost_cells(ids, values);
}

predicate growing_list<t>(box id; list<t> elems) = growing_list0(id, ?ids) &*& ghost_cells(ids, elems) &*& length(ids) == length(elems);
predicate has_at<t>(handle h; box listId, int index, t elem) = has_at0(h, listId, index, ?id) &*& [_]ghost_cell(id, elem);

lemma box create_growing_list<t>()
    requires true;
    ensures growing_list<t>(result, {});
{
    create_box result = growing_list0({});
    close growing_list(result, {});
    return result;
}

lemma void growing_list_add<t>(box id, t value)
    requires growing_list<t>(id, ?elems);
    ensures growing_list<t>(id, append(elems, {value}));
{
    open growing_list(id, elems);
    int newId = ghost_cells_add(value);
    consuming_box_predicate growing_list0(id, ?ids)
    perform_action add(newId) {}
    producing_box_predicate growing_list0(append(ids, {newId}));
    close growing_list(id, append(elems, {value}));
}

lemma handle create_has_at<t>(box id, int index)
    requires growing_list<t>(id, ?elems) &*& 0 <= index &*& index < length(elems);
    ensures growing_list<t>(id, elems) &*& has_at<t>(result, id, index, nth(index, elems));
{
    open growing_list(id, elems);
    ghost_cells_lookup(index);
    consuming_box_predicate growing_list0(id, ?cellIds)
    perform_action noop() {}
    producing_fresh_handle_predicate has_at0(index, nth(index, cellIds));
    close growing_list<t>(id, elems);
    close has_at(?handleId, id, index, nth(index, elems));
    return handleId;
}

lemma void match_has_at_<t>(handle handleId)
    requires has_at<t>(handleId, ?id, ?index, ?elem) &*& growing_list<t>(id, ?elems);
    ensures growing_list<t>(id, elems) &*& has_at<t>(handleId, id, index, elem) &*& 0 <= index &*& index < length(elems) &*& nth(index, elems) == elem;
{
    open growing_list(id, elems);
    open has_at(handleId, id, index, elem);
    consuming_box_predicate growing_list0(id, ?elems0)
    consuming_handle_predicate has_at0(handleId, index, ?cellId)
    perform_action noop() {}
    producing_handle_predicate has_at0(handleId, index, cellId);
    ghost_cells_match(index);
    close growing_list(id, elems);
    close has_at(handleId, id, index, elem);
}

lemma void match_has_at<t>(box id)
    requires growing_list<t>(id, ?elems) &*& has_at<t>(?handleId, id, ?index, ?elem);
    ensures growing_list<t>(id, elems) &*& has_at<t>(handleId, id, index, elem) &*& 0 <= index &*& index < length(elems) &*& nth(index, elems) == elem;
{
    match_has_at_(handleId);
}

@*/
