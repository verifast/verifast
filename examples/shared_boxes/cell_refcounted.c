/*
Example taken from "A Discipline for Program Verification based on Backpointers
and its Use in Observational Disjointness".
*/

#include "gotsmanlock.h"
//@ #include "assoclist.gh"
#include "stdlib.h"
//@ #include "listex.gh"

struct cell {
  int lock;
  int value;
  int refcount;
};

struct cell_client {
  struct cell* cell;
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
  
box_class rcbox(int value, int refcount, list<pair<handle, real> > owners) {
  invariant distinct(keys(owners)) == true &*& refcount == length(owners);
  
  action noop();
    requires true;
    ensures value == old_value && refcount == old_refcount && owners == old_owners;
    
  action set_value(int x);
    requires refcount == 1 && mem(head(actionHandles), keys(owners)) && length(actionHandles) == 1;
    ensures value == x && refcount == 1 && owners == old_owners;
  
  action relinquish(real f);
    requires mem(head(actionHandles), keys(owners)) && assoc(head(actionHandles), owners) == f && length(actionHandles) == 1; 
    ensures value == old_value && refcount == old_refcount - 1 && owners == remove_assoc(head(actionHandles), old_owners);
  
  handle_predicate is_client(int v, real f) {
    invariant mem(predicateHandle, keys(owners)) == true &*& assoc(predicateHandle, owners) == f &*& value == v;
    
    preserved_by noop() {
    }
    
    preserved_by relinquish(action_f) {
       switch(actionHandles) { case nil: case cons(h, t): switch(t) { case nil: case cons(hh, tt) : assert false; } }
       assert head(actionHandles) != predicateHandle;
       neq_mem_remove(predicateHandle, head(actionHandles), keys(old_owners));
       remove_assoc_preserves_other_entries(predicateHandle, head(actionHandles), old_owners);
    }
    
    preserved_by set_value(action_x) {
      switch(actionHandles) { case nil: case cons(h, t): switch(t) { case nil: case cons(hh, tt) : assert false; } }
      switch(owners) { case nil: case cons(h, t): switch(t) { case nil: case cons(hh, tt): assert false; } }
    }
  }
}

predicate_ctor I(struct cell* c, box id)() = c->refcount |-> ?refcount &*& 0 < refcount &*& rcbox(id, ?value, refcount, ?owners) &*& malloc_block_cell(c) &*& [1 - rsum(values(owners))]lock(&c->lock, I(c, id)) &*& [1 - rsum(values(owners))]c->value |-> value;

predicate cell_client(struct cell_client* client, int value) = 
  client->cell |-> ?c &*& is_client(?ha, ?id, value, ?f) &*& [f]lock(&c->lock, I(c, id)) &*& [f]c->value |-> value &*& malloc_block_cell_client(client); 
@*/
  
struct cell_client* create_cell_client(struct cell* c)
  //@ requires c->value |-> ?value &*& c->lock |-> _ &*& c->refcount |-> _ &*& malloc_block_cell(c);
  //@ ensures result == 0 ? c->value |-> value &*& c->lock |-> _ &*& c->refcount |-> _ &*& malloc_block_cell(c) : cell_client(result, value);
{
  struct cell_client* client = malloc(sizeof(struct cell_client));
  if(client == 0) return 0;
  client->cell = c;
  c->refcount = 1;
  //@ create_box id = rcbox(value, 1, cons(pair(ha, 1r/2), nil)) and_handle ha = is_client(value, 1/2);
  //@ close exists(I(c, id));
  init(&c->lock);
  //@ close I(c, id)();
  release(&c->lock);
  //@ close cell_client(client, value);
  return client;
}

void set_value(struct cell_client* client, int x)
  //@ requires cell_client(client, ?value);
  //@ ensures cell_client(client, x);
{
  //@ open cell_client(client, value);
  //@ assert is_client(?ha, ?id, value, ?f);
  struct cell* c = client->cell;
  acquire(&c->lock);
  //@ open I(c, id)();
  if(c->refcount == 1) {
    /*@
    consuming_box_predicate rcbox(id, value, 1, ?owners)
    consuming_handle_predicate is_client(ha, value, f)
    perform_action set_value(x) {
      switch(owners) { case nil: case cons(h, t): switch(h) { case pair(k, v): } switch(t) { case nil: case cons(hh, tt): } };
    }
    producing_box_predicate rcbox(x, 1, owners)
    producing_handle_predicate is_client(ha, x, f);
    @*/
    //@ merge_fractions c->value |-> _;
    c->value = x;
    //@ close I(c, id)();
    release(&c->lock);
  } else {
    /*@
    consuming_box_predicate rcbox(id, value, ?refcount, ?owners)
    consuming_handle_predicate is_client(ha, value, f)
    perform_action relinquish(f) {
      distinct_remove(ha, keys(owners));
    }
    producing_box_predicate rcbox(value, refcount - 1, remove_assoc(ha, owners));
    @*/
    c->refcount = c->refcount - 1;
    //@ rsum_remove_assoc(ha, owners);
    merge_locks(&c->lock); // todo: change to lemma
    //@ close I(c, id)();
    release(&c->lock);
    struct cell* new_cell = malloc(sizeof(struct cell));
    if(new_cell == 0) abort();
    client->cell = new_cell;
    new_cell->refcount = 1;
    new_cell->value = x;
    //@ create_box id2 = rcbox(x, 1, cons(pair(ha2, 1r/2), nil)) and_handle ha2 = is_client(x, 1/2);
    //@ close exists(I(new_cell, id2));
    init(&new_cell->lock);
    //@ close I(new_cell, id2)();
    release(&new_cell->lock);
  }
  //@ close cell_client(client, x);
}

int get_value(struct cell_client* client)
  //@ requires cell_client(client, ?value);
  //@ ensures cell_client(client, value) &*& result == value;
{
  int result;
  //@ open cell_client(client, value);
  result = client->cell->value;
  //@ close cell_client(client, value);
  return result;
}

void dispose_client(struct cell_client* client)
  //@ requires cell_client(client, ?value);
  //@ ensures true;
{
  //@ open cell_client(client, _);
  struct cell* c = client->cell;
   acquire(&c->lock);
   //@ assert is_client(?ha, ?id, value, ?f);
  //@ open I(c, id)();
  if(c->refcount == 1) {
    /*@
    consuming_box_predicate rcbox(id, value, ?refcount, ?owners)
    consuming_handle_predicate is_client(ha, value, f)
    perform_action noop() {
      switch(owners) { case nil: case cons(h, t): switch(h) { case pair(k, v): } switch(t) { case nil: case cons(hh, tt): } };
    };
    @*/
    //@ dispose_box rcbox(id, _, _, _);
    merge_locks(&c->lock);
    finalize(&c->lock);
    free(client->cell);
    free(client);
  } else {
    /*@
    consuming_box_predicate rcbox(id, value, ?refcount, ?owners)
    consuming_handle_predicate is_client(ha, value, f)
    perform_action relinquish(f) {
      distinct_remove(ha, keys(owners));
    }
    producing_box_predicate rcbox(value, refcount - 1, remove_assoc(ha, owners));
    @*/
    c->refcount = c->refcount - 1;
    //@ rsum_remove_assoc(ha, owners);
    merge_locks(&c->lock); // todo: change to lemma
    //@ close I(c, id)();
    release(&c->lock);
    free(client);
  }
}