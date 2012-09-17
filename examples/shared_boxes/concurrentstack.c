#include "atomics.h"
#include "stdlib.h"
//@ #include "quantifiers.gh"

/*@
lemma_auto(mem(x, append(xs, ys))) void mem_append<t>(list<t> xs, list<t> ys, t x)
  requires true;
  ensures mem(x, append(xs, ys)) == (mem(x, xs) || mem(x, ys));
{
  switch(xs) {
    case nil:
    case cons(h, t): mem_append(t, ys, x);
  }
}@*/

/*
TODO:
  - add actions for adding and removing clients
  - take into account the 'active' bit
  - specify that junk nodes are owned by active clients
*/

//@ predicate list(struct list* l, list<void*> vs);

struct list;

struct list* create_list();
  //@ requires true;
  //@ ensures list(result, nil); 
  
void list_add_first(struct list* l, void* p);
  //@ requires list(l, ?vs);
  //@ ensures list(l, cons(p, vs));
  
struct list* list_remove_all(struct list* l);
  //@ requires list(l, ?vs);
  //@ ensures list(l, nil) &*& result != 0 &*& list(result, vs);

void* list_remove_first(struct list* l);
  //@ requires list(l, ?vs) &*& vs != nil;
  //@ ensures list(l, tail(vs)) &*& result == head(vs); 
  
bool list_contains(struct list* l, void* p);
  //@ requires list(l, ?vs);
  //@ ensures list(l, vs) &*& result == mem(p, vs);

bool list_is_empty(struct list* l);
  //@ requires list(l, ?vs);
  //@ ensures list(l, vs) &*& result == (vs == nil);

void list_dispose(struct list* l);
  //@ requires list(l, _);
  //@ ensures true;

struct node {
  void* data;
  struct node* next;
  //@ struct stack_client* owner;
};

struct stack {
  struct node* top;
  struct stack_client* clients;
};

struct stack_client {
  struct node* hp;
  //@ bool valid;
  bool active;
  struct list* rlist;
  int rcount;
  struct stack_client* next;
  //@ handle myhandle;
};

/*@ 
inductive client_state = client_state(struct stack_client* client, struct node* hp, bool valid, bool active, handle ha);

fixpoint list<struct stack_client*> project_stack_clients(list<client_state> states) {
  switch(states) {
    case nil: return nil;
    case cons(h, nstates):
      return switch(h) {
         case client_state(client, hp, valid, active, ha): return cons(client, project_stack_clients(nstates));
      };
  }
}

lemma void append_project_stack_clients(list<client_state> states1, list<client_state> states2)
  requires true;
  ensures append(project_stack_clients(states1), project_stack_clients(states2)) == project_stack_clients(append(states1, states2));
{
  switch(states1) {
    case nil:
    case cons(h, t):
      switch(h) {
        case client_state(client, hp, valid, active, ha): append_project_stack_clients(t, states2);
      }
  } 
}

fixpoint list<client_state> update_hp(struct stack_client* client, struct node* n, list<client_state> states) {
  switch(states) {
    case nil: return nil;
    case cons(h, nstates):
      return switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          return client == client0 ?
            cons(client_state(client, n, false, active0, ha0), nstates)
          :
            cons(h, update_hp(client, n, nstates));
      };
  }
}

lemma void update_hp_preserves_length(struct stack_client* client, struct node* n, list<client_state> states) 
  requires true;
  ensures length(states) == length(update_hp(client, n, states));
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
          if(client == client0) {
          } else {
            update_hp_preserves_length(client, n, nstates);
          }
      }
  }
}

lemma void update_hp_preserves_clients(struct stack_client* client, struct node* n, list<client_state> states) 
  requires true;
  ensures project_stack_clients(states) == project_stack_clients(update_hp(client, n, states));
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
          if(client == client0) {
          } else {
            update_hp_preserves_clients(client, n, nstates);
          }
      }
  }
}

lemma void update_hp_preserves_handles(struct stack_client* c, struct stack_client* client, struct node* n, list<client_state> states) 
  requires true;
  ensures get_handle(c, states) == get_handle(c, update_hp(client, n, states));
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
          if(client == client0) {
          } else {
            update_hp_preserves_handles(c, client, n, nstates);
          }
      }
  }
}

lemma void update_hp_preserves_other_hps(struct stack_client* c, struct stack_client* client, struct node* n, list<client_state> states) 
  requires c != client;
  ensures get_hp(c, states) == get_hp(c, update_hp(client, n, states));
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
          if(client == client0) {
          } else {
            update_hp_preserves_other_hps(c, client, n, nstates);
          }
      }
  }
}

fixpoint list<client_state> validate_hp(struct stack_client* client, list<client_state> states) {
  switch(states) {
    case nil: return nil;
    case cons(h, nstates):
      return switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          return client == client0 ?
            cons(client_state(client, hp0, true, active0, ha0), nstates)
          :
            cons(h, validate_hp(client, nstates));
      };
  }
}

lemma void validate_hp_preserves_clients(struct stack_client* client, list<client_state> states) 
  requires true;
  ensures project_stack_clients(states) == project_stack_clients(validate_hp(client, states));
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
          if(client == client0) {
          } else {
            validate_hp_preserves_clients(client, nstates);
          }
      }
  }
}

lemma void update_hp_get_hp(struct stack_client* client, struct node* hp, list<client_state> states)
  requires mem(client, project_stack_clients(states)) == true;
  ensures get_hp(client, update_hp(client, hp, states)) == hp;
{
switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0): 
          if(client == client0) {
          } else {
             update_hp_get_hp(client, hp, nstates);
          }
      }
  }
}

lemma void validate_hp_preserves_length(struct stack_client* client, list<client_state> states) 
  requires true;
  ensures length(states) == length(validate_hp(client, states));
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
          if(client == client0) {
          } else {
            validate_hp_preserves_length(client, nstates);
          }
      }
  }
}

lemma void validate_hp_preserves_handles(struct stack_client* c, struct stack_client* client, list<client_state> states) 
  requires true;
  ensures get_handle(c, states) == get_handle(c, validate_hp(client, states));
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
          if(client == client0) {
          } else {
            validate_hp_preserves_handles(c, client, nstates);
          }
      }
  }
}

lemma void validate_hp_preserves_hps(struct stack_client* c, struct stack_client* client, list<client_state> states) 
  requires true;
  ensures get_hp(c, states) == get_hp(c, validate_hp(client, states));
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
          if(client == client0) {
          } else {
            validate_hp_preserves_hps(c, client, nstates);
          }
      }
  }
}

fixpoint struct node* get_hp(struct stack_client* client,  list<client_state> states) {
    switch(states) {
    case nil: return 0;
    case cons(h, nstates):
      return switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          return client == client0 ?
            hp0
          :
            get_hp(client, nstates);
      };
  }
}

fixpoint handle get_handle(struct stack_client* client,  list<client_state> states) {
    switch(states) {
    case nil: return default_value<handle>;
    case cons(h, nstates):
      return switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          return client == client0 ?
            ha0
          :
            get_handle(client, nstates);
      };
  }
}

fixpoint bool no_validated_hps(struct node* node, list<client_state> states) {
  switch(states) {
    case nil: return true;
    case cons(h, nstates):
      return switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0): return (hp0 != node || ! valid0) && no_validated_hps(node, nstates);
      };
  }
}

fixpoint bool is_good_retired(list<pair<struct node*, struct stack_client*> > junk, struct stack_client* owner, struct node* retired)
{
  return mem(pair(retired, owner), junk);
}
@*/

/*@
predicate clients(struct stack_client* client, struct stack_client* client2; list<client_state> client_states) =
  client == client2 ?
    client_states == nil
  :
    client != 0 &*& client->hp |-> ?hp &*& client->active |-> ?active &*& [1/2]client->myhandle |-> ?ha &*& client->valid |-> ?valid &*& client->next |-> ?next &*& clients(next, client2, ?nclient_states) &*& 
    client_states == cons(client_state(client, hp, valid, active, ha), nclient_states);

lemma void clients_split(struct stack_client* client, struct stack_client* curr) 
  requires clients(client, 0, ?states) &*& mem(curr, project_stack_clients(states)) == true;
  ensures clients(client, curr, ?states1) &*& clients(curr, 0, ?states2) &*& states == append(states1, states2);
{
  open clients(client, 0, states);
  if(client != 0) {
    if(client != curr) {
      clients_split(client->next, curr);
    }
  } 
}

lemma void clients_merge(struct stack_client* c1, struct stack_client* c2) 
  requires clients(c1, c2, ?states1) &*& clients(c2, 0, ?states2);
  ensures clients(c1, 0, append(states1, states2));
{
  open clients(c1, c2, states1);
  if(c1 != c2) {
      clients_merge(c1->next, c2);
  } 
}

predicate myclients(struct stack* s; list<client_state> client_states) = 
  s->clients |-> ?head_client &*& clients(head_client, 0, client_states);
    
predicate lseg(struct node* from, struct node* to; list<struct node*> nodes, list<void*> vs) =
  from == to ?
    nodes == nil &*& vs == nil
  :
    from != 0 &*& from->data |-> ?data &*& from->next |-> ?next &*& from->owner |-> _ &*& malloc_block_node(from) &*&
    lseg(next, to, ?nnodes, ?nvs) &*& nodes == cons(from, nnodes) &*& vs == cons(data, nvs);

lemma void lseg_split(struct node* from, struct node* to, struct node* n)
  requires lseg(from, to, ?nodes, ?vs) &*& mem(n, nodes) == true;
  ensures lseg(from, n, ?nodes1, ?vs1) &*& lseg(n, to, ?nodes2, ?vs2) &*& n != to &*& append(nodes1, nodes2) == nodes && append(vs1, vs2) == vs &*& length(vs1) == index_of(n, nodes);
{
  open lseg(from, to, nodes, vs);
  if(from == to) {
  } else {
    if(from == n) {
    } else {
      lseg_split(from->next, to, n);
    }
  }
}

lemma void lseg_merge(struct node* a, struct node* b)
  requires lseg(a, b, ?ns1, ?vs1) &*& lseg(b, 0, ?ns2, ?vs2);
  ensures lseg(a, 0, append(ns1, ns2), append(vs1, vs2)) ;
{
  open lseg(a, b, ns1, vs1);
  if(a != b) {
    lseg_merge(a->next, b);
  }
}

predicate is_node(pair<struct node*, struct stack_client*> p) = 
  switch(p) {
    case pair(n, client): return n->next |-> _ &*& n->data |-> _ &*& n->owner |-> client &*& malloc_block_node(n);
  };

box_class stack_box(struct stack* s, predicate(list<void*>) I) {
  invariant s->top |-> ?top &*& lseg(top, 0, ?nodes, ?vs) &*& 
            myclients(s, ?client_states) &*& foreach(?junk, is_node) &*& I(vs);
  
  action noop();
    requires true;
    ensures (top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk);
  
  action push(struct node* new_node, void* v);
    requires true;
    ensures (top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk) 
            ||
            (top == new_node && nodes == cons(new_node, old_nodes) && vs == cons(v, old_vs) && client_states == old_client_states && junk == old_junk);
  
  action pop(struct stack_client* client);
    requires true;
    ensures (top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk) 
            ||
            (old_nodes != nil && top == (nodes == nil ? (void*) 0 : nth(0, nodes)) && nodes == tail(old_nodes) && vs == tail(old_vs) && client_states == old_client_states && junk == cons(pair(old_top, client), old_junk));
  
  action set_hazard_pointer(struct stack_client* client, struct node* n);
    requires mem(client, project_stack_clients(client_states)) == true && actionHandle == get_handle(client, client_states);
    ensures (top == old_top && nodes ==old_nodes && vs == old_vs && client_states == update_hp(client, n, old_client_states) && junk == old_junk);
  
  action validate_hazard_pointer(struct stack_client* client);
    requires mem(client, project_stack_clients(client_states)) == true;
    ensures (get_hp(client, client_states) != old_top && top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk) 
            ||
            (get_hp(client, client_states) == old_top && top == old_top && nodes == old_nodes && vs == old_vs && client_states == validate_hp(client, old_client_states) && junk == old_junk);
  
  action release_node(struct stack_client* client, struct node* n);
    requires mem(client, project_stack_clients(client_states))  && mem(pair(n, client), junk) && actionHandle == get_handle(client, client_states) &&
             no_validated_hps(n, client_states);
    ensures top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == remove(pair(n, client), old_junk);
  
  handle_predicate dummy_handle() {
    invariant true;
    
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(client) { }
    preserved_by set_hazard_pointer(client, n) { }
    preserved_by validate_hazard_pointer(client) { }
    preserved_by release_node(client, n) { }
  }
  
  handle_predicate basic_client_handle(struct stack_client* client, list<struct node*> retired) {
    invariant mem(client,  project_stack_clients(client_states)) == true &&
              forall(retired, (is_good_retired)(junk, client)) && 
              get_handle(client, client_states) == predicateHandle
              ;
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
      }
    }
    preserved_by set_hazard_pointer(action_client, action_n) {
      update_hp_preserves_clients(action_client, action_n, old_client_states);
      update_hp_preserves_length(action_client, action_n, old_client_states);
      update_hp_preserves_handles(client, action_client, action_n, old_client_states);
    }
    preserved_by validate_hazard_pointer(action_client) {
      validate_hp_preserves_clients(action_client, old_client_states);
      validate_hp_preserves_length(action_client, old_client_states);
      validate_hp_preserves_handles(client, action_client, old_client_states);
    }
    preserved_by release_node(action_client, action_n) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          mem_remove(pair(action_n, action_client), pair(n, client), old_junk);
        }
      }
    }
  }
  
  handle_predicate hazard_pointer_set(struct stack_client* client, list<struct node*> retired, struct node* hp) {
    invariant mem(client,  project_stack_clients(client_states)) == true &&
              forall(retired, (is_good_retired)(junk, client)) && 
              get_handle(client, client_states) == predicateHandle &&
              get_hp(client, client_states) == hp;
              
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
      }
    }
    preserved_by set_hazard_pointer(action_client, action_n) {
      update_hp_preserves_clients(action_client, action_n, old_client_states);
      update_hp_preserves_other_hps(client, action_client, action_n, old_client_states);
      update_hp_preserves_length(action_client, action_n, old_client_states);
      update_hp_preserves_handles(client, action_client, action_n, old_client_states);
    }
    preserved_by validate_hazard_pointer(action_client) {
      validate_hp_preserves_clients(action_client, old_client_states);
      validate_hp_preserves_hps(client, action_client, old_client_states);
      validate_hp_preserves_length(action_client, old_client_states);
      validate_hp_preserves_handles(client, action_client, old_client_states);
    }
    preserved_by release_node(action_client, action_n) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          mem_remove(pair(action_n, action_client), pair(n, client), old_junk);
        }
      }
    }
  }
  
  handle_predicate was_top(struct stack_client* client, list<struct node*> retired, bool success, struct node* t) {
    invariant mem(client,  project_stack_clients(client_states)) == true &&
              forall(retired, (is_good_retired)(junk, client)) && 
              get_handle(client, client_states) == predicateHandle &&
              (! success || get_hp(client, client_states) == t) &&
              (!success || mem(t, nodes) || mem(pair(t, client), junk));
              
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
      }
      assume(false);
    }
    preserved_by set_hazard_pointer(action_client, action_n) {
      update_hp_preserves_clients(action_client, action_n, old_client_states);
      update_hp_preserves_other_hps(client, action_client, action_n, old_client_states);
      update_hp_preserves_length(action_client, action_n, old_client_states);
      update_hp_preserves_handles(client, action_client, action_n, old_client_states);
    }
    preserved_by validate_hazard_pointer(action_client) {
      validate_hp_preserves_clients(action_client, old_client_states);
      validate_hp_preserves_hps(client, action_client, old_client_states);
      validate_hp_preserves_length(action_client, old_client_states);
      validate_hp_preserves_handles(client, action_client, old_client_states);
    }
    preserved_by release_node(action_client, action_n) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          mem_remove(pair(action_n, action_client), pair(n, client), old_junk);
        }
      }
      assume(false);
    }
  }
  
  handle_predicate was_top_with_next(struct stack_client* client, list<struct node*> retired, struct node* t, struct node* tn) {
    invariant mem(client,  project_stack_clients(client_states)) == true &&
              forall(retired, (is_good_retired)(junk, client)) && 
              get_handle(client, client_states) == predicateHandle &&
              get_hp(client, client_states) == t &&
              (mem(t, nodes) || mem(pair(t, client), junk));
              
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
      }
      assume(false);
    }
    preserved_by set_hazard_pointer(action_client, action_n) {
      update_hp_preserves_clients(action_client, action_n, old_client_states);
      update_hp_preserves_other_hps(client, action_client, action_n, old_client_states);
      update_hp_preserves_length(action_client, action_n, old_client_states);
      update_hp_preserves_handles(client, action_client, action_n, old_client_states);
    }
    preserved_by validate_hazard_pointer(action_client) {
      validate_hp_preserves_clients(action_client, old_client_states);
      validate_hp_preserves_hps(client, action_client, old_client_states);
      validate_hp_preserves_length(action_client, old_client_states);
      validate_hp_preserves_handles(client, action_client, old_client_states);
    }
    preserved_by release_node(action_client, action_n) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          mem_remove(pair(action_n, action_client), pair(n, client), old_junk);
        }
      }
      assume(false);
    }
  }
  
  handle_predicate is_good_client_phase2(struct stack_client* client, list<struct node*> retired, list<struct node*> hazards) {
    invariant mem(client,  project_stack_clients(client_states)) == true &&
              forall(retired, (is_good_retired)(junk, client)) && 
              get_handle(client, client_states) == predicateHandle //&&
              // forall n in retired :: ! n in hazards 
             // forall(retired, (is_safe))
              ;
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
      }
    }
    preserved_by set_hazard_pointer(action_client, action_n) {
      update_hp_preserves_clients(action_client, action_n, old_client_states);
      update_hp_preserves_length(action_client, action_n, old_client_states);
      update_hp_preserves_handles(client, action_client, action_n, old_client_states);
    }
    preserved_by validate_hazard_pointer(action_client) {
      validate_hp_preserves_clients(action_client, old_client_states);
      validate_hp_preserves_length(action_client, old_client_states);
      validate_hp_preserves_handles(client, action_client, old_client_states);
    }
    preserved_by release_node(action_client, action_n) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          mem_remove(pair(action_n, action_client), pair(n, client), old_junk);
        }
      }
    }
  }
  
  handle_predicate is_good_client(struct stack_client* client, list<struct node*> retired, struct stack_client* curr, int i) {
    invariant mem(client,  project_stack_clients(client_states)) == true &&
              forall(retired, (is_good_retired)(junk, client)) &&
              get_handle(client, client_states) == predicateHandle &&
              (curr != 0 ? 
                // nth(i, project_stack_clients(client_states)) == curr &&
                // 0 <= i && i < length(client_states) &&
                 mem(curr,  project_stack_clients(client_states)) == true
              : 
                true);
    
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
      }
    }
    preserved_by set_hazard_pointer(action_client, action_n) {
      update_hp_preserves_clients(action_client, action_n, old_client_states);
      update_hp_preserves_length(action_client, action_n, old_client_states);
      update_hp_preserves_handles(client, action_client, action_n, old_client_states);
    }
    preserved_by validate_hazard_pointer(action_client) {
      validate_hp_preserves_clients(action_client, old_client_states);
      validate_hp_preserves_length(action_client, old_client_states);
      validate_hp_preserves_handles(client, action_client, old_client_states);
    }
    preserved_by release_node(action_client, action_n) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          mem_remove(pair(action_n, action_client), pair(n, client), old_junk);
        }
      }
    }
  }
}
@*/

/*@
predicate stack_client(struct stack* s, real f, predicate(list<void*>) I, struct stack_client* client) =
  [f]stack_box(?id, s, I) &*& client != 0 &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& 
  list(rlist, ?retired) &*& client->rcount |-> length(retired) &*& basic_client_handle(ha, id, client, retired);
@*/

/*@
predicate_family stack_push_pre(void* index)();
predicate_family stack_push_post(void* index)();

typedef lemma void stack_push_lemma(predicate(list<void*> vs) I, void* data)();
  requires stack_push_pre(this)() &*& I(?vs);
  ensures stack_push_post(this)() &*& I(cons(data, vs));
@*/

void stack_push(struct stack* s, struct stack_client* client, void* data)
  //@ requires stack_client(s, ?f, ?I, client) &*& is_stack_push_lemma(?lem, I, data) &*& stack_push_pre(lem)();
  //@ ensures stack_client(s, f, I, client) &*& stack_push_post(lem)();
{
  struct node* new_node = malloc(sizeof(struct node));
  if(new_node == 0) abort();
  new_node->data = data;
  while(true)
    /*@ invariant stack_client(s, f, I, client) &*& new_node->next |-> _ &*& new_node->data |-> data &*& new_node->owner |-> _ &*& malloc_block_node(new_node) &*& is_stack_push_lemma(lem, I, data) &*& stack_push_pre(lem)();
    @*/
  {
    //@ open stack_client(s, f, I, client);
    //@ assert [f]stack_box(?id, s, I);
    //@ assert basic_client_handle(?ha, id, client, ?retired);
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate basic_client_handle(ha, client, retired)
    perform_action noop() atomic
    {
      @*/ struct node* t = atomic_load_pointer(&s->top); /*@
    } 
    producing_handle_predicate basic_client_handle(client, retired);
    @*/
    new_node->next = t;
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate basic_client_handle(ha, client, retired)
    perform_action push(new_node, data) atomic
    {
      @*/ struct node* old = atomic_compare_and_set_pointer(&s->top, t, new_node); /*@
      if(old == t) {
        lem();
      }
    } 
    producing_handle_predicate basic_client_handle(client, retired);
    @*/
    //@ close stack_client(s, f, I, client);
    if(old == t) {
      //@ leak is_stack_push_lemma(lem, I, data);
      return;
    }
  }
}

bool stack_try_pop(struct stack* s, struct stack_client* client, void** out)
  //@ requires stack_client(s, ?f, ?I, client) &*& pointer(out, _);
  //@ ensures stack_client(s, f, I, client) &*& pointer(out, ?res);
{
  while(true)
    //@ invariant stack_client(s, f, I, client) &*& pointer(out, _);
  {
    //@ open stack_client(s, f, I, client);
  //  //@ assert is_hprec(?ha, ?id, hpr);
    /*@
    consuming_box_predicate stack_box(?id, s, I)
    consuming_handle_predicate basic_client_handle(?ha, client, ?retired)
    perform_action noop() atomic
    {
      @*/ struct node* t = atomic_load_pointer(&s->top); /*@
    } 
    producing_handle_predicate basic_client_handle(client, retired);
    @*/
    if(t == 0) {
      //@ close stack_client(s, f, I, client);
      return false;
    }
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate basic_client_handle(ha, client, retired)
    perform_action set_hazard_pointer(client, t) atomic
    {
      open myclients(_, ?states);
      assert clients(?head, 0, states);
      clients_split(head, client);
      assert clients(head, client, ?states1); 
      open clients(client, 0, ?states2);
      @*/ atomic_set_pointer(&client->hp, t); /*@
      client->valid = false;
      clients_merge(head, client);
      assume(update_hp(client, t, states) == append(states1, update_hp(client, t, states2)));
      update_hp_get_hp(client, t, states);
      update_hp_preserves_handles(client, client, t, states);
      update_hp_preserves_clients(client, t, states);
    } 
    producing_handle_predicate hazard_pointer_set(client, retired, t);
    @*/
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate hazard_pointer_set(ha, client, retired, t)
    perform_action validate_hazard_pointer(client) atomic
    {
      open lseg(_, _, _, _);
      @*/ struct node* tmp = atomic_load_pointer(&s->top); /*@
      if(tmp == t) {
        open myclients(_, ?states_);
        assert clients(?head_, 0, states_);
        clients_split(head_, client);
        assert clients(head_, client, ?states1_);
        assert clients(client, 0, ?states2_);
        client->valid = true;
        clients_merge(head_, client);
        assert clients(head_, 0, ?poststates_);
        assume(validate_hp(client, states_) == append(states1_, validate_hp(client, states2_)));
        validate_hp_preserves_hps(client, client, states_);
        validate_hp_preserves_handles(client, client, states_);
        validate_hp_preserves_clients(client, states_);
      } else {
      }
    } 
    producing_handle_predicate was_top(client, retired, tmp == t, tmp);
    @*/
    if(tmp != t) {
      /*@
      consuming_box_predicate stack_box(id, s, I)
      consuming_handle_predicate was_top(ha, client, retired, false, tmp)
      perform_action noop() atomic
      {
        @*/ ; /*@
      } 
      producing_handle_predicate basic_client_handle(client, retired);
      @*/
      //@ close stack_client(s, f, I, client);
    } else {
      /*@
      consuming_box_predicate stack_box(id, s, I)
      consuming_handle_predicate was_top(ha, client, retired, true, t)
      perform_action noop() atomic
      {
        assert s->top |-> ?top;
        assert foreach(?junk, is_node);
        if(mem(pair(t, client), junk)) {
          foreach_remove(pair(t, client), junk);
          open is_node(pair(t, client));
        } else {
          lseg_split(top, 0, t);
        }
        @*/ struct node* n = atomic_load_pointer(&t->next); /*@
        close node_next(t, _);
        assert n == t->next;
        if(mem(pair(t, client), junk)) {
          close is_node(pair(t, client));
          foreach_unremove(pair(t, client), junk);
        } else {
          lseg_merge(top, t);
        }
      }
      producing_handle_predicate was_top_with_next(client, retired, t, n);
      @*/
      /*@
      consuming_box_predicate stack_box(id, s, I)
      consuming_handle_predicate was_top_with_next(ha, client, retired, t, n)
      perform_action pop(client) atomic
      {
        open lseg(_, _, ?nodes_, ?vs_);
        assert t != 0;
        open lseg(_, _, _, _);
        @*/ struct node* old = atomic_compare_and_set_pointer(&s->top, t, n); /*@
        close stack_top(s, _);
        if(old == t) {
          open exists(?junk_);
          close exists(cons(t, junk_));
          close is_node(t);
          close foreach(cons(t, junk_), is_node);
          assert length(nodes_) != 0;
          assert length(vs_) != 0;
          assert s->top == n;
          if(tail(nodes_) == nil) {
            assert n == 0;
          } else {
          }
        } else {
        }
      }
      producing_handle_predicate is_junk(old == t, t, hpr);
      @*/
      //@ assume(false);
      if(old == t) {
        /*@
        consuming_box_predicate stack_box(id, s, I)
        consuming_handle_predicate is_junk(ha, true, t, hpr)
        perform_action noop() atomic
        {
          assert foreach(?junk__, _);
          foreach_remove(t, junk__);
          @*/ void* data = atomic_load_pointer(&t->data); /*@
          close is_node(t);
          foreach_unremove(t, junk__);
        }
        producing_handle_predicate is_hprec(hpr);
        @*/
        retire_node(hpr, t);
        //@ close stack_worker(s, f, I, hpr);
        *out = data;
        return true;
      } else {
        //@ assume(false);
        //@ close stack_worker(s, f, I, hpr);
        //@ leak stack_box_handle(_, ha);
      }
    }
  }
} 


void* phase2(struct stack* s, struct stack_client* client, struct list* plist)
  //@ requires [?f]stack_box(?id, s, ?I) &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& list(rlist, ?retired) &*& client->rcount |-> length(retired) &*& list(plist, ?hazards) &*& is_good_client_phase2(ha, id, client, retired, hazards);
  //@ ensures [f]stack_box(id, s, I) &*& client->rlist |-> rlist &*& [1/2]client->myhandle |-> ha &*& list(rlist, ?retired2) &*& client->rcount |-> length(retired2) &*& is_good_client(ha, id, client, retired2, 0, 0);
{
  struct list* tmplist = list_remove_all(client->rlist);
  client->rcount = 0;
  while(! list_is_empty(tmplist))
    //@ invariant [f]stack_box(id, s, I) &*& list(rlist, ?newretired) &*& client->rcount |-> length(newretired) &*& client->rlist |-> rlist  &*& list(tmplist, ?nodes) &*& list(plist, hazards);//is_good_client_phase2(ha, id, client, retired, hazards);
  {
    struct node* curr = list_remove_first(tmplist);
    if(list_contains(plist, curr)) {
      list_add_first(client->rlist, curr);
      client->rcount++;
    } else {
      /*@
      consuming_box_predicate stack_box(id, s, I)
      consuming_handle_predicate is_good_client(ha, client, append(newretired, nodes), curr, i)
      perform_action release_node(client, curr) atomic
      {
        @*/ ; /*@
      }
      producing_handle_predicate is_good_client(client, retired, curr, i + 1);
      @*/
      free(curr);
    }
  }
}

void scan(struct stack* s, struct stack_client* client)
  //@ requires [?f]stack_box(?id, s, ?I) &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& list(rlist, ?retired) &*& client->rcount |-> length(retired) &*& is_good_client(ha, id, client, retired, 0, 0);
  //@ ensures [f]stack_box(id, s, I) &*& client->rlist |-> ?rlist2 &*& [1/2]client->myhandle |-> ha &*& list(rlist, ?retired2) &*& client->rcount |-> length(retired2) &*& is_good_client(ha, id, client, retired2, 0, 0);
{
  // phase1
  struct list* plist = create_list();
  /*@
  consuming_box_predicate stack_box(id, s, I)
  consuming_handle_predicate is_good_client(ha, client, retired, 0, 0)
  perform_action noop() atomic
  { 
    open myclients(_, _);
    open clients(_, _, _);
  @*/ struct stack_client* curr = atomic_load_pointer(&s->clients); /*@
  }
  producing_handle_predicate is_good_client(client, retired, curr, 0);
  @*/
  //@ int i = 0;
  while(curr != 0) 
    //@ invariant [f]stack_box(id, s, I) &*& 0 <= i &*& list(plist, ?hps) &*& is_good_client(ha, id, client, retired, curr, i);
  {
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate is_good_client(ha, client, retired, curr, i)
    perform_action noop() atomic
    {
      open myclients(_, _);
      assert clients(?head, _,  ?states);
      clients_split(head, curr);
      @*/ struct node* hp = atomic_load_pointer(&curr->hp); /*@
      struct stack_client* currnext = curr->next;
      open clients(currnext, 0, _);
      clients_merge(head, curr);
    }
    producing_handle_predicate is_good_client(client, retired, curr, i + 1);
    @*/
    if(hp != 0) {
      list_add_first(plist, hp);
    }
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate is_good_client(ha, client, retired, curr, i + 1)
    perform_action noop() atomic
    {
      open myclients(_, _);
      assert clients(?head_, _,  ?states_);
      clients_split(head_, curr);
      assert clients(head_, curr, ?states1);
      assert clients(curr, 0, ?states2);
      struct stack_client* old_curr = curr;
      open clients(curr, 0, _);
      @*/ curr = atomic_load_pointer(&curr->next); /*@
      open clients(curr, 0, _);
      clients_merge(head_, old_curr);
      append_project_stack_clients(states1, states2);
    }
    producing_handle_predicate is_good_client(client, retired, curr, i + 1);
    @*/
    //@ i++;
  }
  // phase 2
  phase2(s, client, plist);  
  //@ assume(false);
}

