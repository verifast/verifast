/*
Implementation of ghost-lists (with distinct elements) via shared boxes.
*/

//@# include "listex.gh"
//@# include "assoclist.gh"
//@# include "quantifiers.gh"
//@# include "strong_ghost_lists.gh"

/*@
fixpoint handle update_owner(handle new_owner, handle old_owner) {
  return new_owner;
}

fixpoint bool ok(list<int> xs, list<pair<int, handle> > owners, handle predicateHandle, int x) {
  return ! mem(x, xs) && mem(x, keys(owners)) && assoc(x, owners) == predicateHandle;
}

lemma void update_owners_preserves_keys(list<pair<int, handle> > owners, list<int> to_update, handle new_owner)
  requires true;
  ensures keys(update_owners(owners, to_update, new_owner)) == keys(owners);
{
  switch(owners){ 
    case nil:
    case cons(h, t):
      switch(h) { case pair(k, v): }
      update_owners_preserves_keys(t, to_update, new_owner);
  }
}

lemma void update_owners_preserves_other_values(list<pair<int, handle> > owners, list<int> to_update, handle new_owner, int x)
  requires ! mem(x, to_update);
  ensures assoc(x, owners) == assoc(x, update_owners(owners, to_update, new_owner));
{
  switch(owners){ 
    case nil:
    case cons(h, t):
      switch(h) { case pair(k, v): }
      update_owners_preserves_other_values(t, to_update, new_owner, x);
  }
}

lemma void update_owners_sets_values(list<pair<int, handle> > owners, list<int> to_update, handle new_owner, int x)
  requires mem(x, to_update) == true && mem(x, keys(owners));
  ensures new_owner == assoc(x, update_owners(owners, to_update, new_owner));
{
  switch(owners){ 
    case nil:
    case cons(h, t):
      switch(h) { case pair(k, v): if(k != x) update_owners_sets_values(t, to_update, new_owner, x); }
      
  }
}

box_class glist(list<int> xs, list<pair<int, handle> > owners) {
  invariant distinct(xs) == true &*& distinct(keys(owners)) == true;
  action noop();
    requires true;
    ensures xs == old_xs && owners == old_owners;
  
  action add(int x, handle new_owner);
    requires ! mem(x, xs) && mem(x, keys(owners)) && assoc(x, owners) == head(actionHandles) && 0 < length(actionHandles);
    ensures xs == cons(x, old_xs) && owners == update_entry<int, handle>(x, (update_owner)(new_owner), old_owners);
  
  action remove(int x, handle new_owner);
    requires  mem(x, xs) && mem(x, keys(owners)) && assoc(x, owners) == head(actionHandles) && 0 < length(actionHandles);
    ensures xs == remove(x, old_xs) && owners == update_entry<int, handle>(x, (update_owner)(new_owner), old_owners);
 
  action change_owners(list<int> updated_keys, handle new_owner);
    requires forall(updated_keys, (ok)(xs, owners, head(actionHandles))) == true && length(actionHandles) > 0;
    ensures xs == old_xs && owners == update_owners(old_owners, updated_keys, new_owner);
  
  handle_predicate in(int x) {
    invariant mem(x, xs) == true &*& mem(x, keys(owners)) == true &*& assoc(x, owners) == predicateHandle;
    
    preserved_by noop() {
    }
    
    preserved_by add(action_x, action_new_owner) {
      update_entry_preserves_keys(action_x, (update_owner)(action_new_owner), old_owners);
      update_entry_preserves_other_values(x, action_x, (update_owner)(action_new_owner), old_owners);
    }
    
    preserved_by remove(action_x, action_new_owner) {
      switch(actionHandles) { case nil:  case cons(h, t): }
      update_entry_preserves_keys(action_x, (update_owner)(action_new_owner), old_owners);
      if(action_x != x) {
        update_entry_preserves_other_values(x, action_x, (update_owner)(action_new_owner), old_owners);
        neq_mem_remove(x, action_x, old_xs);
      }
    }
    
    preserved_by change_owners(to_update, new_owner) {
      switch(actionHandles) { case nil: case cons(h, t): }
      update_owners_preserves_keys(old_owners, to_update, new_owner);
      if(mem(x, to_update)) {
        forall_elim(to_update, (ok)(old_xs, old_owners, head(actionHandles)), x);
      } else {
        update_owners_preserves_other_values(old_owners, to_update, new_owner, x);
      }
    }
  }
  
  handle_predicate out(list<int> set) {
    invariant distinct(set) == true &*& forall(set, (ok)(xs, owners, predicateHandle)) == true;
    
    preserved_by noop() {
    }
    
    preserved_by add(action_x, action_new_owner) {
      switch(actionHandles) { case nil: case cons(h, t): }
      if(! forall(set, (ok)(xs, owners, predicateHandle))) {
        int ex = not_forall(set, (ok)(xs, owners, predicateHandle));
        forall_elim(set, (ok)(old_xs, old_owners, predicateHandle), ex);
        update_entry_preserves_other_values(ex, action_x, (update_owner)(action_new_owner), old_owners);
      }
    }
    
    preserved_by remove(action_x, action_new_owner) {
      switch(actionHandles) { case nil: case cons(h, t): }
      if(! forall(set, (ok)(xs, owners, predicateHandle))) {
        int ex = not_forall(set, (ok)(xs, owners, predicateHandle));
        forall_elim(set, (ok)(old_xs, old_owners, predicateHandle), ex);
        neq_mem_remove(ex, action_x, old_xs);
        update_entry_preserves_other_values(ex, action_x, (update_owner)(action_new_owner), old_owners);
      }
    }
    
    preserved_by change_owners(updated, new_owner) {
      switch(actionHandles) { case nil: case cons(h, t): }
      if(! forall(set, (ok)(xs, owners, predicateHandle))) {
        int ex = not_forall(set, (ok)(xs, owners, predicateHandle));
        forall_elim(set, (ok)(old_xs, old_owners, predicateHandle), ex);
        update_owners_preserves_keys(old_owners, updated, new_owner); 
        if(! mem(ex, updated)) 
          update_owners_preserves_other_values(old_owners, updated, new_owner, ex); 
        else {
          forall_elim(updated, (ok)(old_xs, old_owners, head(actionHandles)), ex);
        }
      }
    }
  }
}

predicate strong_ghost_list(box id, list<int> xs) = glist(id, xs, ?owners);
predicate member(box id, int x) = in(_, id, x);
predicate nonmembers(box id, list<int> xs) = out(_, id, xs);

fixpoint list<pair<int, handle> > add_handle(list<int> xs, handle ha) {
  switch(xs) {
    case nil: return nil;
    case cons(h, t): return cons(pair(h, ha), add_handle(t, ha));
  }
}

lemma_auto void keys_add_handle(list<int> xs, handle ha) 
  requires true;
  ensures keys(add_handle(xs, ha)) == xs;
{
  switch(xs) {
    case nil:
    case cons(h, t): keys_add_handle(t, ha);
  }
}

lemma_auto void assoc_add_handle(int x, list<int> xs, handle ha) 
  requires mem(x, xs) == true;
  ensures assoc(x, add_handle(xs, ha)) == ha;
{
  switch(xs) {
    case nil:
    case cons(h, t): if(x != h) assoc_add_handle(x, t, ha);
  }
}

lemma_auto void add_handle_lemma(list<int> initial_out, handle ha) 
  requires true;
  ensures forall(initial_out, (ok)(nil, add_handle(initial_out, ha), ha)) == true;
{
  if(! forall(initial_out, (ok)(nil, add_handle(initial_out, ha), ha))) {
    int ex = not_forall(initial_out, (ok)(nil, add_handle(initial_out, ha), ha));
  } 
}

lemma box create_ghost_list<t>(list<int> initial_out)
    requires distinct(initial_out) == true;
    ensures strong_ghost_list(result, nil) &*& nonmembers(result, initial_out);
{
  close exists(nil);
  create_box id = glist(nil, add_handle(initial_out, ha)) and_handle ha = out(initial_out);
  close strong_ghost_list(id, nil);
  close nonmembers(id, initial_out);
  return id;
}

lemma void strong_ghost_list_add(box id, int x)
    requires strong_ghost_list(id, ?xs) &*& nonmembers(id, ?set) &*& mem(x, set) == true;
    ensures strong_ghost_list(id, cons(x, xs)) &*& nonmembers(id, remove(x, set)) &*& member(id, x);
{
  open strong_ghost_list(id, xs);
  open nonmembers(id, set);
  assert out(?ha1, id, set);
  handle ha2 = create_handle glist_handle(id);
  consuming_box_predicate glist(id, xs, ?owners)
  consuming_handle_predicate out(ha1, set)
  consuming_handle_predicate glist_handle(ha2)
  perform_action add(x, ha2) {
    forall_elim(set, (ok)(xs, owners, ha1), x);
    distinct_remove(x, set);
    update_entry_preserves_keys(x, (update_owner)(ha2), owners);
    if(! forall(remove(x, set), (ok)(cons(x, xs), update_entry(x, (update_owner)(ha2), owners), ha1))) {
      int ex = not_forall(remove(x, set), (ok)(cons(x, xs), update_entry(x, (update_owner)(ha2), owners), ha1));
      distinct_mem_remove(x, set);
      mem_remove_mem(ex, x, set);
      forall_elim(set, (ok)(xs, owners, ha1), ex);
      if(x != ex) {
       update_entry_preserves_other_values(ex, x, (update_owner)(ha2), owners);
      } 
    }
  }
  producing_box_predicate glist(cons(x, xs), update_entry(x, (update_owner)(ha2), owners))
  producing_handle_predicate out(ha1, remove(x, set))
  producing_handle_predicate in(ha2, x);
  close member(id, x);
  close nonmembers(id, remove(x, set));
  close strong_ghost_list(id, cons(x, xs));
}

lemma void strong_ghost_list_remove(box id, int x)
    requires strong_ghost_list(id, ?xs) &*& member(id, x);
    ensures strong_ghost_list(id, remove(x, xs)) &*& nonmembers(id, cons(x, nil));
{
  open strong_ghost_list(id, xs);
  open member(id, x);
  assert in(?ha, id, x);
  consuming_box_predicate glist(id, xs, ?owners)
  consuming_handle_predicate in(ha, x)
  perform_action remove(x, ha) 
  {
   distinct_remove(x, xs);
   distinct_mem_remove(x, xs);
  }
  producing_box_predicate glist(remove(x, xs), update_entry(x, (update_owner)(ha), owners))
  producing_handle_predicate out(ha, cons(x, nil));
  close strong_ghost_list(id, remove(x, xs));
  close nonmembers(id, cons(x, nil));
}

lemma void strong_ghost_list_member_handle_lemma(box id, int x)
    requires strong_ghost_list(id, ?xs) &*& member(id, x);
    ensures strong_ghost_list(id, xs) &*& member(id, x) &*& mem(x, xs) == true;
{
  open strong_ghost_list(id, xs);
  open member(id, x);
  assert in(?ha, id, x);
  consuming_box_predicate glist(id, xs, ?owners)
  consuming_handle_predicate in(ha, x)
  perform_action noop() {
  }
  producing_box_predicate glist(xs, owners)
  producing_handle_predicate in(ha, x);
  close strong_ghost_list(id, xs);
  close member(id, x);
}

lemma void strong_ghost_list_nonmember_handle_lemma(box id, int x)
    requires strong_ghost_list(id, ?xs) &*& nonmembers(id, ?nonmembers) &*& mem(x, nonmembers) == true;
    ensures strong_ghost_list(id, xs) &*& nonmembers(id, nonmembers) &*& ! mem(x, xs);
{
  open strong_ghost_list(id, xs);
  open nonmembers(id, nonmembers);
  assert out(?ha, id, nonmembers);
  consuming_box_predicate glist(id, xs, ?owners)
  consuming_handle_predicate out(ha, nonmembers)
  perform_action noop() {
    forall_elim(nonmembers, (ok)(xs, owners, ha), x);
  }
  producing_handle_predicate out(ha,  nonmembers);
  close strong_ghost_list(id, xs);
  close nonmembers(id, nonmembers);
}

fixpoint list<pair<int, handle> > update_owners(list<pair<int, handle> > owners, list<int> to_update, handle new_owner) {
  switch(owners) {
    case nil: return nil;
    case cons(h, t):
      return switch(h) { case pair(k, v): return cons(mem(k, to_update) ? pair(k, new_owner) : pair(k, v), update_owners(t, to_update, new_owner)); };
  }
}

lemma void distinct_append<t>(list<t> l1, list<t> l2)
  requires distinct(append(l1, l2)) == true;
  ensures distinct(l1) && distinct(l2);
{
  switch(l1) {
    case nil:
    case cons(h, t): distinct_append(t, l2);
  }
}

lemma void mem_distinct_append<t>(list<t> l1, list<t> l2, t x)
  requires distinct(append(l1, l2)) == true;
  ensures ! (mem(x, l1) && mem(x, l2));
{
  switch(l1) {
    case nil:
    case cons(h, t): mem_distinct_append(t, l2, x);
  }
}

lemma void strong_ghost_list_nonmember_split(box id, list<int> l1, list<int> l2)
    requires strong_ghost_list(id, ?xs) &*& nonmembers(id, ?nonmembers) &*& append(l1, l2) == nonmembers;
    ensures strong_ghost_list(id, xs)  &*& nonmembers(id, l1) &*& nonmembers(id, l2);
{
  open strong_ghost_list(id, xs);
  open nonmembers(id, nonmembers); 
  handle new_owner = create_handle glist_handle(id);
  consuming_box_predicate glist(id, xs, ?owners)
  consuming_handle_predicate out(?old_owner, nonmembers)
  consuming_handle_predicate glist_handle(new_owner)
  perform_action change_owners(l1, new_owner) {
    distinct_append(l1, l2);
    update_owners_preserves_keys(owners, l1, new_owner);
    forall_append(l1, l2, (ok)(xs, owners, old_owner));
    if(! forall(l1, (ok)(xs, update_owners(owners, l1, new_owner), new_owner))) {
      int ex = not_forall(l1, (ok)(xs, update_owners(owners, l1, new_owner), new_owner));
      forall_elim(nonmembers, (ok)(xs, owners, old_owner), ex);
      mem_distinct_append(l1, l2, ex);
      assert !mem(ex, l2);
      update_owners_sets_values(owners, l1, new_owner, ex);
    }
    if(! forall(l2, (ok)(xs, update_owners(owners, l1, new_owner), old_owner))) {
      int ex = not_forall(l2, (ok)(xs, update_owners(owners, l1, new_owner), old_owner));
      forall_elim(nonmembers, (ok)(xs, owners, old_owner), ex);
      mem_distinct_append(l1, l2, ex);
      update_owners_preserves_other_values(owners, l1, new_owner, ex);
    }
  }
  producing_box_predicate glist(xs, update_owners(owners, l1, new_owner))
  producing_handle_predicate out(old_owner,  l2)
  producing_handle_predicate out(new_owner, l1);
  close strong_ghost_list(id, xs);
  close nonmembers(id, l2);
  close nonmembers(id, l1);
}

lemma t not_distinct_append_distinct<t>(list<t> l1, list<t> l2)
  requires distinct(l1) && distinct(l2);
  ensures distinct(append(l1, l2)) || (mem(result, l1) && mem(result, l2));
{
  switch(l1) {
    case nil: return default_value<t>;
    case cons(h, t):
      if(mem(h, l2)) 
        return h;
      else
        return not_distinct_append_distinct(t, l2);
  }
}

lemma void strong_ghost_list_nonmember_merge(box id, list<int> l1, list<int> l2)
    requires strong_ghost_list(id, ?xs) &*& nonmembers(id, l1) &*& nonmembers(id, l2);
    ensures strong_ghost_list(id, xs)  &*& nonmembers(id, append(l1, l2));
{
  open strong_ghost_list(id, xs);
  open nonmembers(id, l1);
  assert out(?ha1, id, l1);
  open nonmembers(id, l2);
  assert out(?ha2, id, l2);
  consuming_box_predicate glist(id, xs, ?owners)
  consuming_handle_predicate out(ha1, l1)
  consuming_handle_predicate out(ha2, l2)
  perform_action change_owners(l1, ha2) {
    update_owners_preserves_keys(owners, l1, ha2);
    int e = not_distinct_append_distinct(l1, l2);
    if(! distinct(append(l1, l2))) {
      forall_elim(l1, (ok)(xs, owners, ha1), e);
      forall_elim(l2, (ok)(xs, owners, ha2), e);
    }
    if(! forall(append(l1, l2), (ok)(xs, update_owners(owners, l1, ha2), ha2))) {
      int ex = not_forall(append(l1, l2), (ok)(xs, update_owners(owners, l1, ha2), ha2));
      mem_append(ex, l1, l2);
      if(mem(ex, l1)) {
        forall_elim(l1, (ok)(xs, owners, ha1), ex);
        update_owners_sets_values(owners,l1, ha2, ex);
      } else {
        forall_elim(l2, (ok)(xs, owners, ha2), ex);
        update_owners_preserves_other_values(owners,l1, ha2, ex);
      }
    }
  }
  producing_box_predicate glist(xs, update_owners(owners, l1, ha2))
  producing_handle_predicate out(ha2,  append(l1, l2));
  close strong_ghost_list(id, xs);
  close nonmembers(id, append(l1, l2));
}
@*/