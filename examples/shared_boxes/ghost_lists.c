/*
Implementation of ghost-lists (elements need not be distinct) via shared boxes.
*/

//@# include "listex.gh"
//@# include "assoclist.gh"
//@# include "nat.gh"

/*@
fixpoint bool is_permutation<t>(list<t> xs, list<t> ys)
{
  switch(xs) {
    case nil: return ys == nil;
    case cons(h, t):
      return mem(h, ys) && is_permutation(t, remove(h, ys));
  }
}

lemma_auto void is_permutation_reflexive(list<int> xs) 
  requires true;
  ensures is_permutation(xs, xs) == true;
{
  switch(xs) {
    case nil: 
    case cons(h, t): 
      switch(t) {
        case nil:
        case cons(h0, t0):
          is_permutation_reflexive(t);
      }
  }
}

fixpoint int count_eq<t>(list<t> xs, t x) {
  switch(xs) {
    case nil: return 0;
    case cons(h, t): return (h == x ? 1 : 0) + count_eq(t, x); 
  }
}

lemma void mem_remove<t>(list<t> xs, t x, t y)
  requires mem(x, remove(y, xs)) == true;
  ensures mem(x, xs) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
     if(h == x) {
     } else {
      if(h == y) {
      } else {
        mem_remove(t, x, y);
      }
     }
  }
}

lemma void not_mem_remove<t>(list<t> xs, t x, t y)
  requires mem(x, remove(y, xs)) == false && x != y;
  ensures mem(x, xs) == false;
{
  switch(xs) {
    case nil:
    case cons(h, t):
     if(h == x) {
     } else {
      if(h == y) {
      } else {
        not_mem_remove(t, x, y);
      }
     }
  }
}

lemma void remove_comm<t>(list<t> xs, t x, t y) 
  requires true;
  ensures remove(x, remove(y, xs)) == remove(y, remove(x, xs));
{
  switch(xs) {
    case nil: 
    case cons(h, t):
      if(h == x) {
      } else {
        if(h == y) {
        } else {
          remove_comm(t, x, y);
        }
      }
  }
}

lemma void is_perm_remove<t>(list<t> xs, list<t> ys, t x)
  requires is_permutation(xs, ys) == true;
  ensures is_permutation(remove(x, xs), remove(x, ys)) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(x == h) {
      } else {
        neq_mem_remove(h, x, ys);
        remove_comm(ys, h, x);
        is_perm_remove(t, remove(h, ys), x);  
      }
  }
}

lemma void is_perm_mem<t>(list<t> xs, list<t> ys, t x) 
  requires is_permutation(xs, ys) == true;
  ensures mem(x, xs) == mem(x, ys);
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(h == x) {
      } else {
         switch(ys) {
           case nil:
           case cons(h0, t0):
             is_perm_mem(t, remove(h, ys), x);
             if(mem(x, t)) {
               mem_remove(ys, x, h);
             } else {
               not_mem_remove(ys, x, h);
             }
         }
      }
  }
}

lemma void is_perm_transitive<t>(list<t> xs, list<t> ys, list<t> zs)
  requires is_permutation(xs, ys) == true &*& is_permutation(ys, zs)== true;
  ensures is_permutation(xs, zs) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      is_perm_mem(ys, zs, h);
      is_perm_remove(ys, zs, h);
      is_perm_transitive(t, remove(h, ys), remove(h, zs));
  }
}

lemma void is_perm_cons_remove<t>(list<t> xs, t x)
  requires mem(x, xs) == true;
  ensures is_permutation(xs, cons(x, remove(x, xs))) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(h != x) {
        is_perm_cons_remove(t, x);
      }
  }
}

lemma void is_perm_symmetric_core<t>(nat n, list<t> xs, list<t> ys)
  requires is_permutation(xs, ys) == true &*& length(xs) == int_of_nat(n);
  ensures is_permutation(ys, xs) == true;
{
  switch(n) {
    case zero:
      switch(xs) { case nil: case cons(hx, tx): }
      switch(ys) { case nil: case cons(hy, ty): }
    case succ(n0):
     switch(xs) {
       case nil: switch(ys) { case nil: case cons(hy, ty): }
       case cons(hx, tx):
         switch(ys) {
           case nil:
           case cons(hy, ty):
             is_perm_symmetric_core(n0, tx, remove(hx, ys));
             if(hx == hy) {
             } else {
               is_perm_cons_remove(ys, hx);
               is_perm_transitive(ys, cons(hx, remove(hx, ys)), xs);
             }
         }
     }
  }
}

lemma void is_perm_symmetric<t>(list<t> xs, list<t> ys)
  requires is_permutation(xs, ys) == true;
  ensures is_permutation(ys, xs) == true;
{
  is_perm_symmetric_core(nat_of_int(length(xs)), xs, ys); 
}

box_class glist(list<pair<handle, void*> > xs) {
  invariant distinct(keys(xs)) == true &*& foreach(keys(xs), is_handle);
  
  action noop();
    requires true;
    ensures xs == old_xs;
  
  action add(void* x);
    requires true;
    ensures xs == cons(pair(actionHandle, x), old_xs);
  
  action remove(void* x);
    requires true;
    ensures xs == remove(pair(actionHandle, x), old_xs);
  
  handle_predicate ticket(void *x) {
    invariant mem(pair(predicateHandle, x), xs) == true;
    
    preserved_by noop() {
    }
    
    preserved_by add(action_x) {
    }
    
    preserved_by remove(action_x) {
        neq_mem_remove(pair(predicateHandle, x), pair(actionHandle, action_x), old_xs);
    }
  }
}

predicate strong_ghost_list(box id, list<void*> xs) = glist(id, ?mapping) &*& is_permutation(values(mapping), xs) == true;
predicate strong_ghost_list_member_handle(box id, void* d) = ticket(_, id, d);

lemma box create_ghost_list<t>()
    requires true;
    ensures strong_ghost_list(result, nil);
{
  close exists(nil);
  close foreach(nil, is_handle);
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

lemma void strong_ghost_list_add(box id, void* x)
    requires strong_ghost_list(id, ?xs);
    ensures strong_ghost_list(id, cons(x, xs)) &*& strong_ghost_list_member_handle(id, x);
{
  open strong_ghost_list(id, xs);
  handle ha = create_fresh_handle glist_handle(id);
  consuming_box_predicate glist(id, ?mapping)
  consuming_handle_predicate glist_handle(ha)
  perform_action add(x) {
    handles_unique(keys(mapping), ha);
  }
  producing_box_predicate glist(cons(pair(ha, x), mapping))
  producing_handle_predicate ticket(x);
  close strong_ghost_list_member_handle(id, x);
  close strong_ghost_list(id, cons(x, xs));
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

lemma void key_lemma<t1, t2>(list<pair<t1, t2> > map, t1 k, t2 v)
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
            key_lemma(t, k, v);
            if(v == v_) {
              mem_values(k, v, t);
              is_perm_cons_remove(values(t), v);
              is_perm_transitive(values(t), cons(v, remove(v, values(t))), cons(v, values(remove(pair(k, v), t))));
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
    distinct_keys_implies_distinct_entries(mapping);
    assert distinct(mapping) == true;
    remove_distinct_keys_preserves_distinct_keys(mapping, ha, x);
    assert distinct(keys(remove(pair(ha, x), mapping))) == true;
  }
  producing_box_predicate glist(remove(pair(ha, x), mapping))
  producing_handle_predicate glist_handle();
  is_perm_remove(values(mapping), xs, x);
  is_perm_symmetric(values(mapping), xs);
  is_perm_remove(xs, values(mapping), x);
  key_lemma(mapping, ha, x);
  is_perm_transitive(remove(x, xs), remove(x, values(mapping)), values(remove(pair(ha, x), mapping)));
  is_perm_symmetric(remove(x, xs), values(remove(pair(ha, x), mapping)));
  close strong_ghost_list(id, remove(x, xs));
  leak glist_handle(_, _);
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
    is_perm_mem(values(mapping), xs, x);
    mem_values(ha, x, mapping);
  }
  producing_box_predicate glist(mapping)
  producing_handle_predicate ticket(x);
  close strong_ghost_list(id, xs);
  close strong_ghost_list_member_handle(id, x);
}
@*/