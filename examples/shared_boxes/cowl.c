#include "stdlib.h"
#include "gotsmanlock.h"
//@ #include "assoclist.gh"
//@ #include "listex.gh"
#include "cowl.h"

struct node {
  int lock;
  int value;
  int refcount;
  struct node* next;
  //@ list<int> values;
};

struct list {
  struct node* head;
};
/*@
fixpoint real rsum(list<real> fracs) {
  switch(fracs) {
    case nil: return 0r;
    case cons(h, t): return h + rsum(t);
  }
}

lemma void rsum_remove_assoc<t1>(t1 key, list<pair<t1, real> > map)
  requires mem(key, keys(map)) == true;
  ensures rsum(values(remove_assoc(key, map))) == rsum(values(map)) - assoc(key, map);
{
  switch(map) {
    case nil: 
    case cons(h, t): switch(h) { case pair(k, v): if(k != key) rsum_remove_assoc(key, t); }
  }
}

lemma void rsum_update_entry<t1>(t1 key, real new_value, list<pair<t1, real> > map)
  requires mem(key, keys(map)) == true;
  ensures rsum(values(update_entry(key, (update_frac)(new_value), map))) == rsum(values(map)) - assoc(key, map) + new_value;
{
  switch(map) {
    case nil: 
    case cons(h, t): switch(h) { case pair(k, v): if(k != key) rsum_update_entry(key, new_value, t); }
  }
}

fixpoint real update_frac(real new, real old) {
  return new;
}
@*/

/*@
box_class nbox(list<pair<handle, real> > owners) {
  invariant distinct(keys(owners)) == true;
 
  action noop();
    requires true;
    ensures owners == old_owners;
   
  action split_ownership(real f, handle new_ha);
    requires mem(head(actionHandles), keys(owners)) && assoc(head(actionHandles), owners) == f && length(actionHandles) > 1;
    ensures owners == cons(pair(new_ha, f/2), update_entry(head(actionHandles), (update_frac)(f/2), old_owners));
 
  action release();
    requires mem(head(actionHandles), keys(owners)) && length(actionHandles) == 1;
    ensures owners == remove_assoc(head(actionHandles), old_owners);
    
  handle_predicate is_client(real f) {
    invariant mem(predicateHandle, keys(owners)) == true &*& assoc(predicateHandle, owners) == f;
    
    preserved_by noop() {
    }
     
    preserved_by split_ownership(action_f, action_new_ha) {
      switch(actionHandles) { case nil: case cons(h, t): }
      update_entry_preserves_other_values(predicateHandle, head(actionHandles), (update_frac)(action_f/2), old_owners);
    }
    
    preserved_by release() {
      switch(actionHandles) { case nil: assert false; case cons(h, t): switch(t) { case nil: case cons(hh, tt): } }
      neq_mem_remove(predicateHandle, head(actionHandles), keys(old_owners));
      remove_assoc_preserves_other_entries(predicateHandle, head(actionHandles), old_owners);
    }
  } 
}

lemma void foreach_is_handle_distinct(list<handle> l, handle ha)
  requires foreach(l, is_handle) &*& is_handle(ha);
  ensures foreach(l, is_handle) &*& is_handle(ha) &*& ! mem(ha, l);
{
  open foreach(l, is_handle);
  switch(l) {
    case nil:
    case cons(h, t): is_handle_unique(h, ha); foreach_is_handle_distinct(t, ha);
  }
  close foreach(l, is_handle);
}

predicate_ctor I(struct node* n, box id)() = 
  n->refcount |-> ?refcount &*& n->value |-> ?value &*& n->next |-> ?next &*& 
  nbox(id, ?owners) &*& refcount == length(owners) &*& 
  [1-rsum(values(owners))]lock(&n->lock, I(n, id)) &*&
  [1-rsum(values(owners))]n->values |-> ?values &*& head(values) == value &*&
  malloc_block_node(n) &*& foreach(keys(owners), is_handle) &*&
  (next == 0 ? values == cons(value, nil) : is_client_wrapper(next, ?nha, ?nid, ?nf) &*& [nf]next->values |-> ?tail &*& values == cons(value, tail));

predicate is_client_wrapper(struct node* n, handle ha, box id, real f) = is_client(ha, id, f) &*& [f]lock(&n->lock, I(n, id));

predicate list(struct list* l, list<int> values) = 
  l->head |-> ?head &*& malloc_block_list(l) &*&
  head == 0 ? values == nil : is_client_wrapper(head, ?ha, ?id, ?f) &*& [f]head->values |-> values;
@*/

struct list* create_cow_list() 
  //@ requires true;
  //@ ensures result == 0 ? true : list(result, nil);
{
  struct list* l = malloc(sizeof(struct list));
  if (l == 0) return 0;
  l->head = 0;
  //@ close list(l, nil);
  return l;
}

struct list* copy_cow_list(struct list* src)
  //@ requires list(src, ?values);
  //@ ensures list(src, values) &*& result == 0 ? true : list(result, values);
{
  //@ open list(src, values);
  struct list* l = malloc(sizeof(struct list));
  struct node* head = src->head;
  if (l == 0) { 
    return 0;
    //@ close list(src, values);
  }
  l->head = src->head;
  if(src->head != 0) {
    //@ open is_client_wrapper(src->head, ?ha, ?id, ?f);
    acquire(&src->head->lock);
    //@ open I(head, id)();
    //@ handle new_ha = create_fresh_handle nbox_handle(id);
    /*@
    consuming_box_predicate nbox(id, ?owners)
    consuming_handle_predicate is_client(ha, f)
    consuming_handle_predicate nbox_handle(new_ha)
    perform_action split_ownership(f, new_ha) {
      foreach_is_handle_distinct(keys(owners), new_ha);
      close foreach(cons(new_ha, keys(owners)), is_handle);
    }
    producing_box_predicate nbox(cons(pair(new_ha, f/2), update_entry(ha, (update_frac)(f/2), owners)))
    producing_handle_predicate is_client(ha, f/2)
    producing_handle_predicate is_client(new_ha, f/2);
    @*/
    if(src->head->refcount == INT_MAX) abort();
    src->head->refcount += 1;
    //@ rsum_update_entry(ha, f/2, owners);
    //@ close I(head, id)();
    release(&src->head->lock);
    //@ close is_client_wrapper(src->head, ha, id, f/2);
    //@ close is_client_wrapper(head, new_ha, id, f / 2);
  }
  //@ close list(src, values);
  //@ close list(l, values);
  return l;
}

void cow_list_insert(struct list* l, int x)
  //@ requires list(l, ?values);
  //@ ensures list(l, cons(x, values));
{
  //@ open list(l, values);
  struct node* old_head = l->head;
  //@ handle the_handle;
  struct node* new_node = malloc(sizeof(struct node));
  if(new_node == 0) abort();
  new_node->value = x;
  if(l->head != 0) {
    //@ open is_client_wrapper(old_head, ?ha, ?id, ?f);
    //@ the_handle = ha;
  }
  new_node->next = l->head;
  l->head = new_node;
  new_node->refcount = 1;
  //@ new_node->values = cons(x, old_head == 0 ? nil : old_head->values);
  //@ create_box new_id = nbox(cons(pair(new_ha, 1r/2), nil)) and_fresh_handle new_ha = is_client(1r/2);
  //@ close exists(I(new_node, new_id));
  init(&new_node->lock);
  if(new_node->next != 0) {
    //@ close is_client_wrapper(old_head, the_handle, _, _);
  }
  //@ close foreach(nil, is_handle);
  //@ close foreach(cons(new_ha, nil), is_handle); 
  //@ close I(new_node, new_id)();
  release(&new_node->lock);
  //@ close is_client_wrapper(new_node, _, _, _);
  //@ close list(l, cons(x, values));
}

//@ predicate node_set_copy_ghost_args(struct node* n, handle ha, box id, real f) = true;

void cow_list_node_set_copy(struct node* n, int index, int x, struct node* new_node)
  /*@ requires node_set_copy_ghost_args(n, ?ha, ?id, ?f) &*& 0 < f && f < 1 &*& nbox(id, ?owners) &*& [1-rsum(values(owners))]lock(&n->lock, I(n, id)) &*& locked(&n->lock, I(n, id)) &*&
               n->refcount |-> length(owners) &*& n->value |-> ?value &*& n->next |-> ?next &*& 
               [1-rsum(values(owners))]n->values |-> ?values &*& head(values) == value &*&
               malloc_block_node(n) &*& foreach(keys(owners), is_handle) &*&
               0 <= index &*& index < length(values) &*& 
               (next == 0 ? values == cons(value, nil) : is_client_wrapper(next, ?nha, ?nid, ?nf) &*& [nf]next->values |-> ?tail &*& values == cons(value, tail)) &*&
               new_node->refcount |-> _ &*& new_node->next |-> _ &*& new_node->values |-> _ &*& new_node->value |-> _ &*& malloc_block_node(new_node) &*& new_node->lock |-> _; @*/
  //@ ensures is_client_wrapper(new_node, ?new_ha, ?new_id, ?new_frac) &*& [new_frac]new_node->values |-> update(index, x, values);
{
  //@ open node_set_copy_ghost_args(n, ha, id, f);
  new_node->refcount = 1;
  struct node* nxt = n->next;
  //@ handle nxt_handle;
  //@ box nxt_id;
  //@ real nxt_f;
  if(nxt != 0) {
    //@ open is_client_wrapper(nxt, ?nha, ?nid, ?nf);
    //@ nxt_handle = nha;
    //@ nxt_id = nid;
    //@ nxt_f = nf;
    acquire(&nxt->lock);
    //@ open I(nxt, nid)();
  }
  //@ create_box new_id = nbox(cons(pair(new_ha, 1r/2), nil)) and_fresh_handle new_ha = is_client(1r/2); 
  //@ close exists(I(new_node, new_id));
  //@ close foreach(nil, is_handle);
  //@ close foreach(cons(new_ha, nil), is_handle);
  init(&new_node->lock);
  if(index == 0) {
    new_node->value = x;
    new_node->next = nxt;
    if(nxt != 0) {
      if(nxt->refcount == INT_MAX) abort();
      nxt->refcount = nxt->refcount + 1;
      //@ handle additional_handle = create_fresh_handle nbox_handle(nxt_id);
      /*@
      consuming_box_predicate nbox(nxt_id, ?nowners)
      consuming_handle_predicate is_client(nxt_handle, ?g)
      consuming_handle_predicate nbox_handle(additional_handle)
      perform_action split_ownership(g, additional_handle) {
        foreach_is_handle_distinct(keys(nowners), additional_handle);
        close foreach(cons(additional_handle, keys(nowners)), is_handle);
      }
      producing_box_predicate nbox(cons(pair(additional_handle, g/2), update_entry(nxt_handle, (update_frac)(g/2), nowners)))
      producing_handle_predicate is_client(nxt_handle, g/2)
      producing_handle_predicate is_client(additional_handle, g/2);
      @*/
      //@ close is_client_wrapper(nxt, additional_handle, _, _);
      //@ close is_client_wrapper(nxt, nxt_handle, _, _);
      //@ rsum_update_entry(nxt_handle, g/2, nowners);
      //@ close I(nxt, nxt_id)();
      release(&nxt->lock);
    }
    //@ new_node->values = cons(x, tail(values));
    //@ close I(new_node, new_id)();
    //@ close is_client_wrapper(new_node, new_ha, new_id, 1r/2);
  } else {
    new_node->value = n->value;
    //@ new_node->values = update(index, x, values);
    if(nxt != 0) {
      struct node* new_node2 = malloc(sizeof(struct node));
      if(new_node2 == 0) abort();
      new_node->next = new_node2;
      //@ close is_client_wrapper(nxt, _, _, _);
      //@ close node_set_copy_ghost_args(nxt, nxt_handle, nxt_id, nxt_f); 
      cow_list_node_set_copy(nxt, index - 1, x, new_node2);
    } else {
      assert(false);
    }
    //@ close I(new_node, new_id)();
    //@ close is_client_wrapper(new_node, new_ha, new_id, 1r/2); 
  }
  release(&new_node->lock);
  //@ close I(n, id)();
  release(&n->lock);
}

//@ predicate node_set_ghost_args(list<int> values, handle ha, box id, real f) = true;

void cow_list_node_set(struct node* n, int index, int x)
  /*@ requires node_set_ghost_args(?values, ?ha, ?id, ?f) &*& 0 < f && f < 1 &*& [1 -f]lock(&n->lock, I(n, id)) &*& locked(&n->lock, I(n, id)) &*& 
               nbox(id, cons(pair(ha, f), nil)) &*& 
               n->refcount |-> 1 &*& n->value |-> ?value &*& n->next |-> ?next &*& 
               [1-f]n->values |-> update(index, x, values) &*& head(values) == value &*&
               malloc_block_node(n) &*& foreach(cons(ha, nil), is_handle) &*&
               0 <= index &*& index < length(values) &*& 
               (next == 0 ? values == cons(value, nil) : is_client_wrapper(next, ?nha, ?nid, ?nf) &*& [nf]next->values |-> ?tail &*& values == cons(value, tail));
  @*/
  //@ ensures true;
{ 
  //@ open node_set_ghost_args(values, ha, id, f);
  if(index == 0) {
    n->value = x;
    //@ switch(values) { case nil: case cons(h, t): }
    //@ close I(n, id)();
    release(&n->lock);
  } else {
    struct node* nxt = n->next;
    //@ assert is_client_wrapper(nxt, ?nha, ?nid, ?nf);
    //@ open is_client_wrapper(nxt, nha, nid, nf);
    acquire(&nxt->lock);
    //@ open I(nxt, nid)();
    if(nxt->refcount == 1) {
      /*@
      consuming_box_predicate nbox(nid, ?nowners)
      consuming_handle_predicate is_client(nha, nf)
      perform_action noop() {
        switch(nowners) { case nil: assert false; case cons(h, t): switch(t) { case nil: switch(h) { case pair(k, v): } case cons(hh,tt): assert false;} }
      }
      producing_handle_predicate is_client(nha, nf);
      @*/
      //@ list<int> old_values = nxt->values;
      //@ nxt->values = update(index - 1, x, nxt->values);
      //@ close is_client_wrapper(next, nha, nid, nf);
      //@ close I(n, id)();
      release(&n->lock);
      //@ close node_set_ghost_args(old_values, nha, nid, nf);
      cow_list_node_set(nxt, index - 1, x);
    } else {
      nxt->refcount = nxt->refcount - 1;
      /*@
      consuming_box_predicate nbox(nid, ?nowners)
      consuming_handle_predicate is_client(nha, nf)
      perform_action release() {
        distinct_remove(nha, keys(nowners));
      }
      producing_box_predicate nbox(remove_assoc(nha, nowners));
      @*/
      //@ foreach_remove(nha, keys(nowners));
      //@ leak is_handle(nha);
      //@ rsum_remove_assoc(nha, nowners);
      struct node* new_node = malloc(sizeof(struct node));
      if(new_node == 0) abort();
      //@ list<int> old_values = nxt->values;
      n->next = new_node;
      //@ close node_set_copy_ghost_args(nxt, nha, nid, nf);
      merge_locks(&nxt->lock);
      cow_list_node_set_copy(nxt, index - 1, x, new_node);
      //@ close I(n, id)();
      release(&n->lock);
    }
  }
}

void cow_list_set(struct list* l, int i, int x)
  //@ requires list(l, ?values) &*& 0 <= i &*& i < length(values);
  //@ ensures list(l, update(i, x, values));
{
  //@ open list(l, values);
  struct node* head = l->head;
  //@ open is_client_wrapper(head, ?ha, ?id, ?f);
  acquire(&head->lock);
  //@ open I(head, id)();
  //@ assert nbox(id, ?owners);
  if(head->refcount == 1) {
    /*@
    consuming_box_predicate nbox(id, owners)
    consuming_handle_predicate is_client(ha, f)
    perform_action noop() {
      switch(owners) { case nil: assert false; case cons(h, t): switch(t) { case nil: switch(h) { case pair(k, v): } case cons(hh,tt): assert false;} }
    }
    producing_handle_predicate is_client(ha, f);
    @*/
    merge_locks(&head->lock);
    //@ head->values = update(i, x, head->values);
    //@ close node_set_ghost_args(values, ha, id, f);
    cow_list_node_set(head, i, x);
    //@ close is_client_wrapper(head, ha, id, f);
    //@ close list(l, update(i, x, values));
  } else {
    head->refcount--;
    /*@
    consuming_box_predicate nbox(id, owners)
    consuming_handle_predicate is_client(ha, f)
    perform_action release() {
      distinct_remove(ha, keys(owners));
    }
    producing_box_predicate nbox(remove_assoc(ha, owners));
    @*/
    //@ foreach_remove(ha, keys(owners));
    //@ leak is_handle(ha);
    //@ rsum_remove_assoc(ha, owners);
    struct node* new_node = malloc(sizeof(struct node));
    if(new_node == 0) abort();
    l->head = new_node;
    merge_locks(&head->lock);
    //@ close node_set_copy_ghost_args(head, ha, id, f);
    cow_list_node_set_copy(head, i, x, new_node);
    //@ close list(l, update(i, x, values));
  }
}

void cow_list_dispose(struct list* l)
  //@ requires list(l, ?values);
  //@ ensures true;
{
  //@ open list(l, values);
  struct node* curr = l->head;
  while(curr != 0) 
    //@ invariant curr == 0 ? true : is_client_wrapper(curr, ?ha, ?id, ?f) &*& [f]curr->values |-> _;
  {
    //@ assert is_client_wrapper(curr, ?ha, ?id, ?f);
    //@ open is_client_wrapper(curr, ha, id, f);
    acquire(&curr->lock);
    //@ open I(curr, id)();
    curr->refcount--;
    if(curr->refcount == 0) {
      struct node* next = curr->next;
      //@ dispose_box nbox(id, ?owners) and_handle is_client(ha, f);
      //@ switch(owners) { case nil: case cons(h, t): switch(t) { case nil: case cons(hh, tt): } switch(h) { case pair(k, v): assert k == ha; } }
      //@ assert length(owners) == 1;
      merge_locks(&curr->lock);
      finalize(&curr->lock);
      free(curr);
      //@ leak foreach(_, _);
      curr = next;
    } else {
       /*@
      consuming_box_predicate nbox(id, ?owners)
      consuming_handle_predicate is_client(ha, f)
      perform_action release() {
        distinct_remove(ha, keys(owners));
      }
      producing_box_predicate nbox(remove_assoc(ha, owners));
      @*/
      //@ foreach_remove(ha, keys(owners));
      //@ leak is_handle(ha);
      //@ rsum_remove_assoc(ha, owners);
      merge_locks(&curr->lock);
      //@ close I(curr, id)();
      release(&curr->lock);
      break;
    }
  }
  free(l);
}