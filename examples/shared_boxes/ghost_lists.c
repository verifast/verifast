/*
Implementation of ghost-lists (elements need not be distinct) via shared boxes.
*/

//@# include "listex.gh"
//@# include "assoclist.gh"
//@# include "nat.gh"
//@# include "permutations.gh"

/*@
// BOX_CLASS

box_class glist(list<pair<handle, void*> > xs) {
  invariant foreach(keys(xs), is_handle) &*& 
            distinct(keys(xs)) == true; // derivable from foreach
  
  action noop();
    requires true;
    ensures xs == old_xs;
  
  action add(void* x);
    requires true;
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
      switch(actionHandles) { case nil: case cons(h, t): }
      neq_mem_remove(pair(predicateHandle, x), pair(head(actionHandles), action_x), old_xs);
    }
  }
}

// AUXILIARY LEMMAS

lemma void remove_map_keys(list< pair< handle, void*> > map, handle ha, void* x)
  requires distinct(keys(map)) == true &*& mem(pair(ha, x), map) == true;
  ensures keys(remove(pair(ha, x), map)) == remove(ha, keys(map));
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(k, v):
          if(k == ha && v == x) {
          } else {
            remove_map_keys(t, ha, x);
            if(k == ha) {
              mem_keys(ha, x, t);
            }
          }
      }
  }
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

lemma void handles_unique(list<handle> hs, handle ha)
  requires foreach(hs, is_handle) &*& is_handle(ha);
  ensures foreach(hs, is_handle) &*& is_handle(ha) &*& ! mem(ha, hs);
{
  open foreach(hs, is_handle);
  switch(hs) {
    case nil:
    case cons(h, t):
      is_handle_unique(h, ha);
      handles_unique(t, ha);
  }
  close foreach(hs, is_handle);
}

lemma void remove_non_mem_keys_preserves_non_mem_keys<t1, t2>(list< pair<t1, t2> > map, t1 k, t2 v, t1 k_)
  requires ! mem(k_, keys(map));
  ensures ! mem(k_, keys(remove(pair(k, v), map)));
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(kk, vv): 
          if(kk == k && vv == v) {
          } else {
            remove_non_mem_keys_preserves_non_mem_keys(t, k, v, k_);
          }
      }
  }
}

lemma void remove_distinct_keys_preserves_distinct_keys<t1, t2>(list< pair<t1, t2> > map, t1 k, t2 v)
  requires distinct(keys(map)) == true;
  ensures distinct(keys(remove(pair(k, v), map))) == true;
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(k_, v_):
          if(k_ == k && v_ == v) {
          } else {
            remove_distinct_keys_preserves_distinct_keys(t, k, v);
            neq_mem_remove(pair(k_, v_), pair(k, v), t);
            distinct_keys_implies_distinct_entries( map);
	    remove_non_mem_keys_preserves_non_mem_keys(t, k, v, k_);
          }
      }
  }
}

lemma void values_commutes_with_remove_for_permutation<t1, t2>(list<pair<t1, t2> > map, t1 k, t2 v)
  requires mem(pair(k, v), map) == true;
  ensures is_permutation(remove(v, values(map)), values(remove(pair(k, v), map))) == true;
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(k_, v_):
          if(k == k_ && v == v_) {
          } else {
            values_commutes_with_remove_for_permutation(t, k, v);
            if(v == v_) {
              mem_values(k, v, t);
              is_perm_cons_remove(values(t), v);
              is_perm_transitive(values(t), cons(v, remove(v, values(t))), cons(v, values(remove(pair(k, v), t))));
            }
          }
      }
  }
}

// MAIN DEFINITIONS AND LEMMAS

predicate ghost_list(box id, list<void*> xs) = glist(id, ?mapping) &*& is_permutation(values(mapping), xs) == true;
predicate ghost_list_member_handle(box id, void* d) = ticket(_, id, d);

lemma box create_ghost_list<t>()
    requires true;
    ensures ghost_list(result, nil);
{
  close exists(nil);
  close foreach(nil, is_handle);
  create_box id = glist(nil);
  close ghost_list(id, nil);
  return id;
}

lemma void ghost_list_add(box id, void* x)
    requires ghost_list(id, ?xs);
    ensures ghost_list(id, cons(x, xs)) &*& ghost_list_member_handle(id, x);
{
  open ghost_list(id, xs);
  handle ha = create_fresh_handle glist_handle(id);
  consuming_box_predicate glist(id, ?mapping)
  consuming_handle_predicate glist_handle(ha)
  perform_action add(x) {
    handles_unique(keys(mapping), ha);
    close foreach(cons(ha, keys(mapping)), is_handle);
  }
  producing_box_predicate glist(cons(pair(ha, x), mapping))
  producing_handle_predicate ticket(ha, x);
  close ghost_list_member_handle(id, x);
  close ghost_list(id, cons(x, xs));
}


lemma void ghost_list_remove(box id, void* x)
    requires ghost_list(id, ?xs) &*& ghost_list_member_handle(id, x);
    ensures ghost_list(id, remove(x, xs));
{
  open ghost_list(id, xs);
  open ghost_list_member_handle(id, x);
  assert ticket(?ha, id, x);
  consuming_box_predicate glist(id, ?mapping)
  consuming_handle_predicate ticket(ha, x)
  perform_action remove(x) 
  {
    mem_keys(ha, x, mapping);
    distinct_keys_implies_distinct_entries(mapping);
    remove_distinct_keys_preserves_distinct_keys(mapping, ha, x);
    remove_map_keys(mapping, ha, x);
    foreach_remove(ha, keys(mapping));
  }
  producing_box_predicate glist(remove(pair(ha, x), mapping));
  is_perm_remove(values(mapping), xs, x);
  is_perm_symmetric(values(mapping), xs);
  is_perm_remove(xs, values(mapping), x);
  values_commutes_with_remove_for_permutation(mapping, ha, x);
  is_perm_transitive(remove(x, xs), remove(x, values(mapping)), values(remove(pair(ha, x), mapping)));
  is_perm_symmetric(remove(x, xs), values(remove(pair(ha, x), mapping)));
  close ghost_list(id, remove(x, xs));
  leak is_handle(_);
}

lemma void ghost_list_member_handle_lemma(box id, void* x)
    requires ghost_list(id, ?xs) &*& ghost_list_member_handle(id, x);
    ensures ghost_list(id, xs) &*& ghost_list_member_handle(id, x) &*& mem(x, xs) == true;
{
  open ghost_list(id, xs);
  open ghost_list_member_handle(id, x);
  assert ticket(?ha, id, x);
  consuming_box_predicate glist(id, ?mapping)
  consuming_handle_predicate ticket(ha, x)
  perform_action noop() {
    is_perm_mem(values(mapping), xs, x);
    mem_values(ha, x, mapping);
  }
  producing_box_predicate glist(mapping)
  producing_handle_predicate ticket(ha, x);
  close ghost_list(id, xs);
  close ghost_list_member_handle(id, x);
}
@*/