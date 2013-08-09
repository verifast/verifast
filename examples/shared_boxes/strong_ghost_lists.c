/*
Implementation of ghost-lists (with distinct elements) via shared boxes.
*/

//@# include "listex.gh"
//@# include "assoclist.gh"

/*@
box_class glist(list<pair<handle, void*> > xs) {
  invariant distinct(values(xs)) == true;
  
  action noop();
    requires true;
    ensures xs == old_xs;
  
  action add(void* x);
    requires ! mem(pair(head(actionHandles), x), xs);
    ensures xs == cons(pair(head(actionHandles), x), old_xs);
  
  action remove(void* x);
    requires switch(actionHandles) { case nil: return false; case cons(h, t): return t == nil; };
    ensures xs == remove(pair(head(actionHandles), x), old_xs);
  
  handle_predicate ticket(void *x) {
    invariant mem(pair(predicateHandle, x), xs) == true;
    
    preserved_by noop() {
    }
    
    preserved_by add(action_x) {
    }
    
    preserved_by remove(action_x) {
      switch(actionHandles) { case nil: case cons(h, t): };
      neq_mem_remove(pair(predicateHandle, x), pair(head(actionHandles), action_x), old_xs);
    }
  }
}

predicate strong_ghost_list(box id, list<void*> xs) = glist(id, ?mapping) &*& values(mapping) == xs;
predicate strong_ghost_list_member_handle(box id, void* d) = ticket(_, id, d);

lemma box create_ghost_list<t>()
    requires true;
    ensures strong_ghost_list(result, nil);
{
  close exists(nil);
  create_box id = glist(nil);
  close strong_ghost_list(id, nil);
  return id;
}

lemma void not_in_values_implies_not_in_assoc_list<t1, t2>(list<pair<t1, t2> > map, t1 k, t2 v)
  requires ! mem(v, values(map));
  ensures ! mem(pair(k, v), map);
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(k_, v_):
          not_in_values_implies_not_in_assoc_list(t, k, v);
      }
  }
}

lemma void strong_ghost_list_add(box id, void* x)
    requires strong_ghost_list(id, ?xs) &*& ! mem(x, xs);
    ensures strong_ghost_list(id, cons(x, xs)) &*& strong_ghost_list_member_handle(id, x);
{
  open strong_ghost_list(id, xs);
  handle ha = create_handle glist_handle(id);
  consuming_box_predicate glist(id, ?mapping)
  consuming_handle_predicate glist_handle(ha)
  perform_action add(x) {
    assert ! mem(x, values(mapping));
    not_in_values_implies_not_in_assoc_list(mapping, ha, x);
  }
  producing_box_predicate glist(cons(pair(ha, x), mapping))
  producing_handle_predicate ticket(ha, x);
  close strong_ghost_list_member_handle(id, x);
  close strong_ghost_list(id, cons(x, xs));
}

lemma void remove_pair_from_map_remove_value_from_values<t1, t2>(list<pair<t1, t2> > map, t1 k, t2 v)
  requires distinct(values(map)) == true &*& mem(pair(k, v), map) == true;
  ensures values(remove(pair(k, v), map)) == remove(v, values(map));
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(k_, v_):
          if(v != v_ || k != k_) {
            remove_pair_from_map_remove_value_from_values(t, k, v);
            if(v == v_) {
              not_in_values_implies_not_in_assoc_list(t, k, v);
            }
          }
      }
  }
}

lemma void strong_ghost_list_remove(box id, void* x)
    requires strong_ghost_list(id, ?xs) &*& strong_ghost_list_member_handle(id, x);
    ensures strong_ghost_list(id, remove(x, xs));
{
  open strong_ghost_list(id, xs);
  open strong_ghost_list_member_handle(id, x);
  assert ticket(?ha, id, x);
  consuming_box_predicate glist(id, ?mapping)
  consuming_handle_predicate ticket(ha, x)
  perform_action remove(x) 
  {
    remove_pair_from_map_remove_value_from_values(mapping, ha, x);
    distinct_remove(x, xs);
  }
  producing_box_predicate glist(remove(pair(ha, x), mapping));
  close strong_ghost_list(id, remove(x, xs));
}

lemma void strong_ghost_list_member_handle_lemma(box id, void* x)
    requires strong_ghost_list(id, ?xs) &*& strong_ghost_list_member_handle(id, x);
    ensures strong_ghost_list(id, xs) &*& strong_ghost_list_member_handle(id, x) &*& mem(x, xs) == true;
{
  open strong_ghost_list(id, xs);
  open strong_ghost_list_member_handle(id, x);
  assert ticket(?ha, id, x);
  consuming_box_predicate glist(id, ?mapping)
  consuming_handle_predicate ticket(ha, x)
  perform_action noop() {
    mem_values(ha, x, mapping);
  }
  producing_box_predicate glist(mapping)
  producing_handle_predicate ticket(ha, x);
  close strong_ghost_list(id, xs);
  close strong_ghost_list_member_handle(id, x);
}
@*/