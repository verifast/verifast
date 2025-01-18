/*
Treiber stack (with hazard pointers)

TODO:
  - add actions for activating clients
  - take into account the 'active' bit
*/

#include "atomics.h"
#include "stdlib.h"
#include "list.h"
#include "concurrentstack.h"
//@ #include "quantifiers.gh"
//@ #include "listex.gh"
//@ #include "assoclist.gh"

struct node {
  void* data;
  struct node* next;
  //@ struct stack_client* owner;
};

struct stack {
  struct node* top;
  struct stack_client* clients;
  //@ int help;
};

struct stack_client {
  struct node* hp;
  //@ bool valid;
  bool active;
  struct list* rlist;
  int rcount;
  struct stack_client* next;
  //@ handle myhandle;
  //@ real myfrac;
};

/*@ 
inductive client_state = client_state(struct node* hp, bool valid, bool active, handle ha, real myfrac);


fixpoint handle get_handle(client_state state) {
  switch(state) {
    case client_state(hp, valid, active, ha, myf): return ha;
  }
}

fixpoint struct node* get_hp(client_state state) {
  switch(state) {
    case client_state(hp, valid, active, ha, myf): return hp;
  }
}

fixpoint bool is_valid(client_state state) {
  switch(state) {
    case client_state(hp, valid, active, ha, myf): return valid;
  }
}

fixpoint bool is_active(client_state state) {
  switch(state) {
    case client_state(hp, valid, active, ha, myf): return active;
  }
}

fixpoint client_state update_hp(struct node* n, client_state state) {
  switch(state) {
    case client_state(hp, valid, active, ha, myf): return client_state(n, false, active, ha, myf);
  }
}

fixpoint client_state validate_hp(client_state state) {
  switch(state) {
    case client_state(hp, valid, active, ha, myf): return client_state(hp, true, active, ha, myf);
  }
}

fixpoint client_state deactivate(client_state state) {
  switch(state) {
    case client_state(hp, valid, active, ha, myf): return client_state(0, valid, false, ha, myf);
  }
}

fixpoint bool not_has_valid_hp(struct node* n, client_state state) {
  switch(state) {
    case client_state(hp, valid, active, ha, myf): return ! valid || hp != n || ! active; 
  }
}

lemma void foreach2foreachp<t>(list<t>xs, predicate(t;) p)
  requires foreach(xs, p);
  ensures foreachp(xs, p);
{
  open foreach(xs, p);
  switch(xs) {
    case nil:
    case cons(h, t): foreach2foreachp(t, p);
  }
  close foreachp(xs, p);
}

fixpoint bool has_owner(struct stack_client* client, pair<struct node*, struct stack_client*> pr) {
  return snd(pr) == client;
}

predicate client_local(struct stack_client* client, struct stack* s, bool active, real frac, list<pair<struct node*, struct stack_client*> > junk;) = 
  active ? 
    [frac]s->help |-> _
  : 
    [1/2]client->active |-> active &*& [1/2]client->myfrac |-> frac &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& 
    list(rlist, ?retired) &*& client->rcount |-> length(retired) &*& 
    forall(retired, (is_good_retired)(junk, client)) == true &*&
    count(junk, (has_owner)(client)) == length(retired) &*&
    foreachp(retired, two_thirds_data) &*& distinct(retired) == true &*& malloc_block_stack_client(client);

predicate clients(struct stack_client* client, struct stack_client* client2, struct stack* s, list<pair<struct node*, struct stack_client*> > junk; list<pair<struct stack_client*, client_state> > client_states) =
  client == client2 ?
    client_states == nil
  :
    client != 0 &*& client->hp |-> ?hp &*& [1/2]client->active |-> ?active &*& [1/2]client->myhandle |-> ?ha &*& [1/2]client->myfrac |-> ?myfrac &*& 
    client_local(client, s, active, myfrac, junk) &*&
    client->valid |-> ?valid &*& client->next |-> ?next  &*& clients(next, client2, s, junk, ?nclient_states) &*& 
    client_states == cons(pair(client, client_state(hp, valid, active, ha, myfrac)), nclient_states) &*&
    (active || (hp == 0));

predicate myclients(struct stack* s, list<pair<struct node*, struct stack_client*> > junk; list<pair<struct stack_client*, client_state> > client_states) = 
  s->clients |-> ?head_client &*& clients(head_client, 0, s, junk, client_states);
    
predicate lseg(struct node* from, struct node* to; list<struct node*> nodes, list<void*> vs) =
  from == to ?
    nodes == nil &*& vs == nil
  :
    from != 0 &*& from->data |-> ?data &*& from->next |-> ?next &*& from->owner |-> _ &*& malloc_block_node(from) &*&
    lseg(next, to, ?nnodes, ?nvs) &*& nodes == cons(from, nnodes) &*& vs == cons(data, nvs);

/*
LEMMAS
*/

lemma void update_hp_preserves_no_validated_hps(struct node* nn, struct stack_client* client, struct node* n, list<pair<struct stack_client*, client_state> > states) 
  requires no_validated_hps(nn, values(states)) == true;
  ensures no_validated_hps(nn, values(update_entry(client, (update_hp)(n), states))) == true;
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case pair(client0, state0):
          switch(state0) {
            case client_state(hp, valid, active, ha, myf):
              update_hp_preserves_no_validated_hps(nn, client, n, nstates);
          }           
      }
  }
}

lemma void validate_different_hp_preserves_no_validated_hps(struct node* n, struct stack_client* client, list<pair<struct stack_client*, client_state> > states) 
  requires n != get_hp(assoc(client, states)) || ! mem(client, keys(states));
  ensures no_validated_hps(n, values(states)) == no_validated_hps(n, values(update_entry(client, (validate_hp), states)));
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case pair(client0, state0):
          switch(state0){
            case client_state(hp, valid, active, ha, myf): 
              if(client != client0) {
                validate_different_hp_preserves_no_validated_hps(n, client, nstates);
              }
          }
      }
  }
}

lemma void append_no_validated_hps(struct node* n, list<client_state> states1, list<client_state> states2)
  requires no_validated_hps(n, states1) == true &*& no_validated_hps(n, states2) == true;
  ensures no_validated_hps(n, append(states1, states2)) == true;
{
  switch(states1) {
    case nil:
    case cons(h, t):
      switch(h) {
        case client_state(hp0, valid0, active0, ha0, myf0):
        append_no_validated_hps(n, t, states2);
      }
  }
}

fixpoint bool no_validated_hps(struct node* node, list<client_state> states) {
  switch(states) {
    case nil: return true;
    case cons(h, nstates):
      return switch(h) {
        case client_state(hp0, valid0, active0, ha0, myf0): return (hp0 != node || ! valid0 || ! active0) && no_validated_hps(node, nstates);
      };
  }
}

fixpoint bool was_observed_or_no_validated_hps(list<struct node*> observedhazards, list<client_state> states, struct node* node) {
  return mem(node, observedhazards) || no_validated_hps(node, states);
}

lemma void deactivate_preserves_no_validated_hps(list<pair<struct stack_client*, client_state> > states, struct node* node, struct stack_client* cl)
  requires  no_validated_hps(node, values(states)) == true;
  ensures no_validated_hps(node, values(update_entry(cl, (deactivate), states))) == true;
{
  switch(states) {
    case nil:
    case cons(h, t):
       switch(h) {
        case pair(cl0, state0): 
          switch(state0) 
          {
            case client_state(hp0, valid0, active0, ha0, myf0): if(cl0 != cl) { deactivate_preserves_no_validated_hps(t, node, cl); }
          }
      };
  }
}

fixpoint bool is_good_retired(list<pair<struct node*, struct stack_client*> > junk, struct stack_client* owner, struct node* retired)
{
  return retired != 0 && mem(pair(retired, owner), junk);
}

fixpoint bool is_good_junk(list<struct stack_client*> clients, pair<struct node*, struct stack_client*> jnk) {
  return mem(snd(jnk), clients); 
}

lemma void clients_mem(struct stack_client* c1, struct stack_client* c2, struct stack_client* c3)
  requires clients(c1, c2, ?s, ?junk, ?states) &*& c3->hp |-> ?hp;
  ensures clients(c1, c2, s, junk, states) &*& c3->hp |-> hp &*& ! mem(c3, keys(states));
{
  open clients(c1, c2, s, junk, states);
  if(c1 != c2) {
    clients_mem(c1->next, c2, c3);
  }
  close clients(c1, c2, s, junk, states);
}

lemma void clients_distinct(struct stack_client* c1, struct stack_client* c2)
  requires clients(c1, c2, ?s, ?junk, ?states);
  ensures clients(c1, c2, s, junk, states) &*& distinct(keys(states)) == true;
{
  open clients(c1, c2, s, junk, states);
  if(c1 == c2) {
  } else {
    clients_mem(c1->next, c2, c1);
    clients_distinct(c1->next, c2);
  }
  close clients(c1, c2, s, junk, states);
}

lemma void clients_split(struct stack_client* client, struct stack_client* curr) 
  requires clients(client, 0, ?s, ?junk, ?states) &*& mem(curr, keys(states)) == true;
  ensures clients(client, curr, s, junk, ?states1) &*& clients(curr, 0, s, junk, ?states2) &*& states == append(states1, states2) && 
          length(states1) == index_of(curr, keys(states)) &&
          ! mem(curr, keys(states1));
{
  open clients(client, 0, s, junk, states);
  if(client != 0) {
    if(client != curr) {
      clients_split(client->next, curr);
    }
  }
  close clients(client, curr, s, junk, _);
}

lemma void clients_merge(struct stack_client* c1, struct stack_client* c2) 
  requires clients(c1, c2, ?s, ?junk, ?states1) &*& clients(c2, 0, s, junk, ?states2);
  ensures clients(c1, 0, s, junk, append(states1, states2));
{
  open clients(c1, c2, s, junk, states1);
  if(c1 != c2) {
      clients_merge(c1->next, c2);
  } 
}


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
  ensures lseg(a, 0, append(ns1, ns2), append(vs1, vs2));
{
  open lseg(a, b, ns1, vs1);
  if(a != b) {
    lseg_merge(a->next, b);
  }
}

lemma void mem_project_nodes(list<pair<struct node*, struct stack_client*> > junk, struct node* n, struct stack_client* c)
  requires mem(pair(n, c), junk) == true;
  ensures mem(n, keys(junk)) == true;
{
  switch(junk) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(n0, c0):
          if(n0 == n && c0 == c) {
          } else {
            mem_project_nodes(t, n, c);
          }
      }
  }
}

lemma void not_mem_keys(list<pair<struct node*, struct stack_client*> > junk, struct node* n, struct stack_client* c)
  requires ! mem(n, keys(junk));
  ensures ! mem(pair(n, c), junk);
{
  switch(junk) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(n0, c0):
          if(n0 == n && c0 == c) {
          } else {
            not_mem_keys(t, n, c);
          }
      }
  }
}

lemma void junk_mem(list<pair<struct node*, struct stack_client* > > junk, struct node* n)
  requires foreach(junk, is_node) &*& n->next |-> ?nxt;
  ensures foreach(junk, is_node) &*& n->next |-> nxt &*& ! mem(n, keys(junk));
{
  switch(junk) {
    case nil:
    case cons(h, t):
      open foreach(junk, is_node);
      open is_node(h);
      junk_mem(t, n);
      close foreach(junk, is_node);
  }
}

lemma void junk_mem_remove(list<pair<struct node*, struct stack_client* > > junk, struct node* n, struct stack_client* c)
  requires mem(pair(n, c), junk) == true &*& distinct(keys(junk)) == true;
  ensures keys(remove(pair(n, c), junk)) == remove(n, keys(junk)); 
{
  switch(junk) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(n0, c0):
          if(n0 == n && c0 == c) {
          } else {
            junk_mem_remove(t, n, c);
            if(n0 == n) {
              not_mem_keys(t, n, c);
            }
          }
      }
  } 
}

predicate is_node(pair<struct node*, struct stack_client*> p;) = 
  fst(p) != 0 &*& fst(p)->next |-> ?next &*& [1/3]fst(p)->data |-> ?data &*& fst(p)->owner |-> snd(p) &*& malloc_block_node(fst(p));
  
lemma void invalidated_hps_lemma(list<pair<struct stack_client*, client_state> > states, struct stack_client* client) 
  requires mem(client, keys(states)) == true &*& is_valid(assoc(client, states)) == true &*& is_active(assoc(client, states)) == true;
  ensures ! no_validated_hps(get_hp(assoc(client, states)), values(states));
{
  switch(states) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(client0, state0):
          switch(state0) {
              case client_state(hp0, valid0, active0, ha0, myf0):
                if(client == client0) {
                } else {
                  invalidated_hps_lemma(t, client);
                }
            }
      }
  }
}

lemma void foreach_two_thirds_mem(list<struct node*> retired, struct node* n)
  requires foreach(retired, two_thirds_data) &*& [2/3]n->data |-> ?data;
  ensures foreach(retired, two_thirds_data) &*& [2/3]n->data |-> data &*& ! mem(n, retired);
{
  open foreach(retired, two_thirds_data);
  switch(retired) {
    case nil:
    case cons(h, t):
      foreach_two_thirds_mem(t, n);
      if(h == n) {
        open two_thirds_data(n);
      }
  }
  close foreach(retired, two_thirds_data);
}

fixpoint list<pair<struct node*, struct stack_client*> > remove_node(list<pair<struct node*, struct stack_client*> > junk, struct node* n) {
  switch(junk) {
    case nil: return nil;
    case cons(h, t): return switch(h) { case pair(nd, owner): return nd == n ? t : cons(h, remove_node(t, n)); };
  }
}

fixpoint struct stack_client* get_owner(struct node* n, list<pair<struct node*, struct stack_client*> > junk) {
  switch(junk) {
    case nil: return 0;
    case cons(h, t): return switch(h) { case pair(nd, owner): return nd == n ? owner : get_owner(n, t); };
  }
}

lemma void junk_remove(list<pair<struct node*, struct stack_client*> > junk, struct node* n)
  requires foreach(junk, is_node) &*& mem(n, keys(junk)) == true;
  ensures foreach(remove_node(junk, n), is_node) &*& is_node(pair(n, get_owner(n, junk))); 
{
  switch(junk) {
    case nil:
    case cons(h, t):
      open foreach(_, _);
      switch(h) {
        case pair(n0, owner0):
          if(n0 == n) {
          } else {
            junk_remove(t, n);
            close foreach(remove_node(junk, n), is_node);
          }
      }
  }
}

lemma void junk_unremove(list<pair<struct node*, struct stack_client*> > junk, struct node* n)
  requires foreach(remove_node(junk, n), is_node) &*& mem(n, keys(junk)) == true &*& is_node(pair(n, ?owner)) &*& get_owner(n, junk) == owner;
  ensures foreach(junk, is_node); 
{
  switch(junk) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(n0, owner0):
          if(n0 == n && owner0 == owner) {
            close foreach(junk, is_node);
          } else {
            open foreach(remove_node(junk, n), is_node);
            junk_unremove(t, n);
            close foreach(junk, is_node);
          }
      }
  }
}

lemma void lseg_mem_zero(struct node* a, struct node* b)
  requires lseg(a, b, ?nodes, ?vs);
  ensures lseg(a, b, nodes, vs) &*& ! mem((void*) 0, nodes);
{
  open lseg(a, b, nodes, vs);
  if(a == b) {
  } else {
      lseg_mem_zero(a->next, b);
  }
}

lemma void lseg_mem(struct node* a, struct node* b, struct node* n)
  requires lseg(a, b, ?nodes, ?vs) &*& n->next |-> ?nxt;
  ensures lseg(a, b, nodes, vs) &*& n->next |-> nxt &*& ! mem(n, nodes);
{
  open lseg(a, b, nodes, vs);
  if(a == b) {
  } else {
    if(a == n) {
    } else {
      lseg_mem(a->next, b, n);
    }
  }
}

/*
BOX
*/

box_class stack_box(struct stack* s, predicate(list<void*>) I) {
  invariant s->top |-> ?top &*& lseg(top, 0, ?nodes, ?vs) &*& 
            foreach(?junk, is_node) &*&
            myclients(s, junk, ?client_states) &*& I(vs) &*&
            malloc_block_stack(s) &*&
            forall(junk, (is_good_junk)(keys(client_states))) == true &*&
            // derived info
            true && (top == 0 ? nodes == nil : nodes != nil && head(nodes) == top) &*&
            distinct(nodes) == true &*&
            forall(nodes, (not_contains)(keys(junk))) == true &*&
            distinct(keys(junk)) == true;
  
  action noop();
    requires true;
    ensures (top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk);
  
  action push(struct node* new_node, void* v);
    requires !mem(new_node, nodes) && ! mem(new_node, keys(junk));
    ensures (top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk) 
            ||
            (top == new_node && nodes == cons(new_node, old_nodes) && vs == cons(v, old_vs) && client_states == old_client_states && junk == old_junk);
  
  action pop(struct stack_client* client);
    requires actionHandles == cons(get_handle(assoc(client, client_states)), nil);
    ensures (top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk) 
            ||
            (old_nodes != nil && top == (nodes == nil ? (void*) 0 : nth(0, nodes)) && nodes == tail(old_nodes) && vs == tail(old_vs) && client_states == old_client_states && junk == cons(pair(old_top, client), old_junk));
  
  action set_hazard_pointer(struct stack_client* client, struct node* n);
    requires mem(client, keys(client_states)) == true && actionHandles == cons(get_handle(assoc(client, client_states)), nil);
    ensures (top == old_top && nodes ==old_nodes && vs == old_vs && client_states == update_entry(client, (update_hp)(n), old_client_states) && junk == old_junk);
  
  action validate_hazard_pointer(struct stack_client* client);
    requires mem(client, keys(client_states)) == true && actionHandles == cons(get_handle(assoc(client, client_states)), nil);
    ensures (get_hp(assoc(client, client_states)) != old_top && top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk) 
            ||
            (get_hp(assoc(client, client_states)) == old_top && old_top != 0 && top == old_top && nodes == old_nodes && vs == old_vs && client_states == update_entry(client, (validate_hp), old_client_states) && junk == old_junk);
  
  action release_node(struct stack_client* client, struct node* n);
    requires mem(client, keys(client_states)) && mem(pair(n, client), junk) && actionHandles == cons(get_handle(assoc(client, client_states)), nil) &&
             no_validated_hps(n, values(client_states));
    ensures top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == remove(pair(n, client), old_junk);
  
  action add_client(struct stack_client* new_client, handle new_client_ha, real myf);
    requires !mem(new_client, keys(client_states));
    ensures top == old_top && nodes == old_nodes && vs == old_vs && junk == old_junk &&
            (client_states == old_client_states || 
            client_states == append(old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil)));
  
  action deactivate(struct stack_client* client);
    requires mem(client, keys(client_states)) && is_active(assoc(client, client_states)) && actionHandles == cons(get_handle(assoc(client, client_states)), nil);
    ensures top == old_top && nodes == old_nodes && vs == old_vs && junk == old_junk &&
            (client_states == update_entry(client, (deactivate), old_client_states));
  
  handle_predicate dummy_handle() {
    invariant true;
    
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(client) { }
    preserved_by set_hazard_pointer(client, n) { }
    preserved_by validate_hazard_pointer(client) { }
    preserved_by release_node(client, n) { }
    preserved_by add_client(new_client, new_client_ha, myf) { }
    preserved_by deactivate(action_client) { }
  }
  
  handle_predicate is_client(struct stack_client* client) {
    invariant mem(client,  keys(client_states)) == true;
    
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) { }
    preserved_by set_hazard_pointer(action_client, n) { }
    preserved_by validate_hazard_pointer(action_client) { }
    preserved_by release_node(action_client, n) { }
    preserved_by add_client(new_client, new_client_ha, myf) { 
      append_keys(old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil));
      mem_append(client, keys(old_client_states), cons(new_client, nil));
    }
    preserved_by deactivate(action_client) { }
  }
  
  handle_predicate basic_client_handle(struct stack_client* client, list<struct node*> retired) extends is_client {
    invariant forall(retired, (is_good_retired)(junk, client)) && 
              get_handle(assoc(client, client_states)) == predicateHandle &&
              is_active(assoc(client, client_states)) == true &&
              count(junk, (has_owner)(client)) == length(retired);
              
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
      }
    }
    preserved_by set_hazard_pointer(action_client, action_n) { }
    preserved_by validate_hazard_pointer(action_client) { }
    preserved_by release_node(action_client, action_n) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          neq_mem_remove( pair(n, client), pair(action_n, action_client), old_junk);
        }
      }
      count_remove(old_junk, (has_owner)(client), pair(action_n, action_client));
    }
    preserved_by add_client(new_client, new_client_ha, myf) {
      assoc_append_l(client, old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil));
    }
    preserved_by deactivate(action_client) { }
  }
  
  handle_predicate hazard_pointer_set(struct stack_client* client, list<struct node*> retired, struct node* t) extends basic_client_handle {
    invariant get_hp(assoc(client, client_states)) == t;
              
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) { }
    preserved_by set_hazard_pointer(action_client, action_n) { }
    preserved_by validate_hazard_pointer(action_client) { }
    preserved_by release_node(action_client, action_n) { }
    preserved_by add_client(new_client, new_client_ha, myf) { 
      assoc_append_l(client, old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil));
    }
    preserved_by deactivate(action_client) { }
  }
  
  handle_predicate was_top(struct stack_client* client, list<struct node*> retired, struct node* t) extends hazard_pointer_set {
    invariant true && (true && t != 0) &&
              (is_valid(assoc(client, client_states)) && is_active(assoc(client, client_states))) &&
              (mem(t, nodes) || mem(t, keys(junk)));
              
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      switch(old_nodes) { case nil: case cons(hh, tt): }
    }
    
    preserved_by set_hazard_pointer(action_client, action_n) { }
    
    preserved_by validate_hazard_pointer(action_client) { }
    
    preserved_by release_node(action_client, action_n) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          neq_mem_remove(pair(n, client), pair(action_n, action_client), old_junk);
        }
      }
      
      if(mem(t, old_nodes)) {
      } else {
        if(action_n != t) {
          junk_mem_remove(old_junk, action_n, action_client);
          neq_mem_remove(t, action_n, keys(old_junk));
        } else {
          invalidated_hps_lemma(old_client_states, client);
        }
      }
    }
    preserved_by add_client(new_client, new_client_ha, myf) { 
     assoc_append_l(client, old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil));
    }
    preserved_by deactivate(action_client) { }
  }
  
  handle_predicate was_top_with_next(struct stack_client* client, list<struct node*> retired, struct node* t, struct node* tn) extends was_top {
    invariant (mem(t, nodes) ?
                (tn != 0 ? 
                  mem(tn, nodes) && index_of(tn, nodes) == index_of(t, nodes) + 1
                :
                  index_of(t, nodes) == length(nodes) - 1
                )
                :
                  true
              );
              
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      switch(old_nodes) { case nil: case cons(hh, tt): }
    }
    preserved_by set_hazard_pointer(action_client, action_n) { }
    preserved_by validate_hazard_pointer(action_client) { }
    preserved_by release_node(action_client, action_n) { }
    preserved_by add_client(new_client, new_client_ha, myf) { }
    preserved_by deactivate(action_client) { }
  }
  
  handle_predicate phase1_handle(struct stack_client* client, list<struct node*> retired, struct stack_client* curr, int index, bool curratindex, list<struct node*> observedhps) extends basic_client_handle {
    invariant 0 <= index && index <= length(client_states) &&
              (curr != 0 ? 
               mem(curr, keys(client_states)) == true &&
               (curratindex ?
                   index < length(client_states) && 
                   nth(index,  keys(client_states)) == curr
                 :
                   0 < index && 
                   nth(index - 1,  keys(client_states)) == curr
               )
              : 
                true) &&
              forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, values(client_states))));

    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) { }
    preserved_by set_hazard_pointer(action_client, action_n) {
      if(!forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, values(client_states))))) {
        struct node* ex = not_forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, values(client_states))));
        forall_elim(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, values(old_client_states))), ex);
        if(!mem(ex, observedhps)) { 
          update_hp_preserves_no_validated_hps(ex, action_client, action_n, take(index, old_client_states)); 
          take_update_entry(action_client, (update_hp)(action_n), old_client_states, index);
          switch(assoc<struct stack_client*, client_state>(action_client, old_client_states)) {
            case client_state(a, b, c, d):
          }
        }
      }
    }
    preserved_by validate_hazard_pointer(action_client) {
      switch(old_nodes) {
        case nil:
        case cons(hh, tt):
      }
      switch(assoc<struct stack_client*, client_state>(action_client, old_client_states)) {
              case client_state(a, b, c, d, e):
      }
        
        if(get_hp(assoc(action_client, old_client_states)) != old_top) {  
        } else {
          
          if(!forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, values(client_states))))) {
             struct node* ex = not_forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, values(client_states))));
             forall_elim(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, values(old_client_states))), ex);
             forall_elim(retired, (is_good_retired)(junk, client), ex);
             if(!mem(ex, observedhps)) {
               take_update_entry(action_client, (validate_hp), old_client_states, index);
               if(ex != old_top) {
                 if(mem(action_client, keys(take(index, old_client_states)))) {
                   take_assoc(index, action_client, old_client_states);
                 }
                 validate_different_hp_preserves_no_validated_hps(ex, action_client, take(index, old_client_states));
               } else {
                 forall_elim(nodes, (not_contains)(keys(junk)), ex);
                 mem_project_nodes(old_junk, ex, client);
               }
             }
           }
        }
    }
    
    preserved_by release_node(action_client, action_n) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          neq_mem_remove(pair(n, client), pair(action_n, action_client), old_junk);
        }
      }
    }
    
    preserved_by add_client(new_client, new_client_ha, myf) { 
      append_keys(old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil));
      append_values(old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil));
      mem_append(client, keys(old_client_states), cons(new_client, nil));
      assoc_append_l(client, old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil));
      if( curr != 0) {
        if(curratindex) {
          nth_append(keys(old_client_states), cons(new_client, nil), index);
        } else {
          nth_append(keys(old_client_states), cons(new_client, nil), index - 1);
        }
      }
      take_append(index, old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil));
    }
  
    preserved_by deactivate(action_client) {
      if(! forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, values(client_states))))) {
        struct node* ex = not_forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, values(client_states))));
        forall_elim(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, values(old_client_states))), ex);
        if(! mem(ex, observedhps)) {
          deactivate_preserves_no_validated_hps(take(index, old_client_states), ex, action_client);
          take_update_entry(action_client, (deactivate), old_client_states, index);
        }
      }
    }
  }
  
  handle_predicate phase2_handle(struct stack_client* client, list<struct node*> retired, list<struct node*> newretired, list<struct node*> todos, list<struct node*> observedhps) extends basic_client_handle {
    invariant forall(todos, (is_good_retired)(junk, client)) && 
              forall(todos, (was_observed_or_no_validated_hps)(observedhps, values(client_states))) &&
              retired == append(newretired, todos);
              
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      if(! forall(todos, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(todos, (is_good_retired)(junk, client));
        forall_elim(todos, (is_good_retired)(old_junk, client), n);
      }
    }
    preserved_by set_hazard_pointer(action_client, action_n) {
      if(!forall(todos, (was_observed_or_no_validated_hps)(observedhps, values(client_states)))) {
        struct node* ex = not_forall(todos, (was_observed_or_no_validated_hps)(observedhps, values(client_states)));
        forall_elim(todos, (was_observed_or_no_validated_hps)(observedhps, values(old_client_states)), ex);
        if(!mem(ex, observedhps)) {
          update_hp_preserves_no_validated_hps(ex, action_client, action_n, old_client_states); 
        }
      }
    }
    preserved_by validate_hazard_pointer(action_client) {
      switch(old_nodes) {
        case nil:
        case cons(hh, tt):
      }
      switch(assoc<struct stack_client*, client_state>(action_client, old_client_states)) {
        case client_state(hp0, valid0, active0, ha0, myf0): 
      }
      if(get_hp(assoc(action_client, old_client_states)) != old_top) {
      } else {
        if(!forall(todos, (was_observed_or_no_validated_hps)(observedhps, values(client_states)))) {
          struct node* ex = not_forall(todos, (was_observed_or_no_validated_hps)(observedhps, values(client_states)));
          forall_elim(todos, (was_observed_or_no_validated_hps)(observedhps, values(old_client_states)), ex);
          forall_elim(todos, (is_good_retired)(junk, client), ex);
          if(!mem(ex, observedhps)) {
            if(ex != old_top) {
              validate_different_hp_preserves_no_validated_hps(ex, action_client, old_client_states); 
            } else {
              forall_elim(nodes, (not_contains)(keys(junk)), ex);
              mem_project_nodes(old_junk, ex, client);
            }
          }
        }
      }
    }
    
    preserved_by release_node(action_client, action_n) {
      if(! forall(todos, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(todos, (is_good_retired)(junk, client));
        forall_elim(todos, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          neq_mem_remove(pair(n, client), pair(action_n, action_client), old_junk);
        }
      }
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          neq_mem_remove(pair(n, client), pair(action_n, action_client), old_junk);
        }
      }
    }
    
    preserved_by add_client(new_client, new_client_ha, myf) { 
      append_keys(old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil));
      append_values(old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil));
      mem_append(client, keys(old_client_states), cons(new_client, nil));
      assoc_append_l(client, old_client_states, cons(pair(new_client, client_state(0, false, true, new_client_ha, myf)), nil));
      if(! forall(todos, (was_observed_or_no_validated_hps)(observedhps, values(client_states))) ) {
        struct node* ex = not_forall(todos, (was_observed_or_no_validated_hps)(observedhps, values(client_states)));
        forall_elim(todos, (was_observed_or_no_validated_hps)(observedhps, values(old_client_states)), ex);
        if(! mem(ex, observedhps)) {
          append_no_validated_hps(ex, values(old_client_states), cons(client_state(0, false, true, new_client_ha, myf), nil));
        }
      }
    }
    preserved_by deactivate(action_client) {
      if(!forall(todos, (was_observed_or_no_validated_hps)(observedhps, values(client_states)))) {
        struct node* ex = not_forall(todos, (was_observed_or_no_validated_hps)(observedhps, values(client_states)));
        forall_elim(todos, (was_observed_or_no_validated_hps)(observedhps, values(old_client_states)), ex);
        if(! mem(ex, observedhps)) {
          deactivate_preserves_no_validated_hps(old_client_states, ex, action_client);
        }
      }
    }
  }
}
@*/

/*@
predicate one_third_data(struct node* n;) =
  [1/3]n->data |-> ?data;

predicate two_thirds_data(struct node* n;) =
  [2/3]n->data |-> ?data;
  
predicate stack_client(struct stack* s, real f, predicate(list<void*>) I, struct stack_client* client) =
  [f]stack_box(?id, s, I) &*& client != 0 &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& 
  list(rlist, ?retired) &*& client->rcount |-> length(retired) &*& basic_client_handle(ha, id, client, retired) &*&
  foreach(retired, two_thirds_data) &*& distinct(retired) == true &*& malloc_block_stack_client(client) &*&
  [1/2]client->myfrac |-> ?myfrac &*& [1/2]client->active |-> true &*& myfrac == f;

predicate stack(struct stack* s, predicate(list<void*>) I) =
  stack_box(?id, s, I) &*& s->help |-> _;
@*/

struct stack* create_stack()
  //@ requires exists<predicate(list<void*>)>(?I) &*& I(nil);
  //@ ensures result == 0 ? I(nil) : stack(result, I);
{
  //@ open exists(I);
  struct stack* s = malloc(sizeof(struct stack));
  if(s == 0) abort();
  s->top = 0;
  s->clients = 0;
  //@ close foreach(nil, is_node);
  //@ create_box id = stack_box(s, I); 
  //@ close stack(s, I);
  return s;
}

struct stack_client* create_client(struct stack* s)
  //@ requires [?f]stack(s, ?I);
  //@ ensures [?g]stack(s, I) &*& result == 0 ? f == g : stack_client(s, ?h, I, result) &*& f == g + h;
{
  //@ open [f]stack(s, I);
  //@ assert [f]stack_box(?id, s, I);
  struct stack_client* new_client = malloc(sizeof(struct stack_client));
  if(new_client == 0) abort();
  //@ handle ha = create_handle stack_box_handle(id);
  new_client->next = 0;
  new_client->hp = 0;
  new_client->valid = false;
  new_client->active = true;
  //@ new_client->myhandle = ha;
  //@ new_client->myfrac = f / 2;
  struct list* l = create_list();
  new_client->rlist = l;
  new_client->rcount = 0;
  /*@
  consuming_box_predicate stack_box(id, s, I)
  consuming_handle_predicate stack_box_handle(ha)
  perform_action add_client(new_client, ha, f/ 2)
  {
    open myclients(_, _, _);
    assert clients(?head, 0,  s, ?junk, ?states);
    assert foreach(junk, is_node);
    clients_mem(head, 0, new_client);
    open clients(head, 0, s, junk, states);
    switch(states) {
        case nil:
        case cons(h, t):
    }
    @*/ struct stack_client* old = atomic_compare_and_set_pointer(&s->clients, 0, new_client); /*@
    if(old == 0) {
      if(! forall(junk, (is_good_junk)(keys(append(states, cons(pair(new_client, client_state(0, false, true, ha, f/2)), nil)))))) {
        pair<struct node*, struct stack_client*> ex = not_forall(junk, (is_good_junk)(keys(append(states, cons(pair(new_client, client_state(0, false, true, ha, f/2)), nil)))));
        forall_elim(junk, (is_good_junk)(keys(states)), ex);
      }
      if(count(junk, (has_owner)(new_client)) != 0) {
        pair<struct node*, struct stack_client*> ex = count_non_zero(junk, (has_owner)(new_client));
        forall_elim(junk, (is_good_junk)(keys(states)), ex);
      }
    } else {
    }
  } 
  producing_handle_predicate if(old == 0) basic_client_handle(ha, new_client, nil) else is_client(ha, old);
  @*/
  if(old == 0) {
    //@ close [f/2]stack(s, I);
    //@ close foreach(nil, two_thirds_data);
    //@ close stack_client(s, f/2, I, new_client); 
    return new_client;
  }
  while(true)
    /*@ invariant [f]stack_box(id, s, I) &*& [f]s->help |-> _ &*& new_client != 0 &*& new_client->next |-> 0 &*& new_client->myhandle |-> ha &*& new_client->valid |-> false &*&
                  new_client->hp |-> 0 &*& new_client->active |-> true &*&  new_client->myfrac |-> f / 2 &*& new_client->rlist |-> ?rlist &*& list(rlist, nil) &*& new_client->rcount |-> 0 &*&
                  malloc_block_stack_client(new_client) &*& is_client(ha, id, old); @*/ 
  {
    struct stack_client* prev = old;
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate is_client(ha, prev)
    perform_action add_client(new_client, ha, f / 2)
    {
      open myclients(s, _, _);
      assert foreach(?junk_, is_node);
      assert clients(?head_, 0, s, junk_, ?states_);
      clients_mem(head_, 0, new_client);
      open clients(head_, 0, s, junk_, states_);
      close clients(head_, 0, s, junk_, states_);
      clients_split(head_, prev);
      assert clients(head_, prev, s, junk_, ?states1);
      open clients(prev, 0, s, junk_, ?states2);
      open clients(_, 0, s, junk_, ?states2_tail);
      switch(states2) {
          case nil:
          case cons(h, t):
      }
      @*/ struct stack_client* new_old = atomic_compare_and_set_pointer(&prev->next, 0, new_client); /*@
      clients_merge(head_, prev);
      if(new_old == 0) {
        append_assoc(states1, states2, cons(pair(new_client, client_state(0, false, true, ha, f/2)), nil));
        assoc_append(new_client, states_, cons(pair(new_client, client_state(0, false, true, ha, f/2)), nil));
        append_keys(states_, cons(pair(new_client, client_state(0, false, true, ha, f/2)), nil));
        mem_append(new_client, keys(states_), keys(cons(pair(new_client, client_state(0, false, true, ha, f/2)), nil)));
        close myclients(s, junk_, ?new_states);
        if(! forall(junk_, (is_good_junk)(keys(new_states)))) {
          pair<struct node*, struct stack_client*> ex = not_forall(junk_, (is_good_junk)(keys(new_states)));
          forall_elim(junk_, (is_good_junk)(keys(states_)), ex);
        }
        if(count(junk_, (has_owner)(new_client)) != 0) {
          pair<struct node*, struct stack_client*> ex = count_non_zero(junk_, (has_owner)(new_client));
          forall_elim(junk_, (is_good_junk)(keys(states_)), ex);
        }
      } else {
        append_keys(states1, states2);
        mem_append(new_old, keys(states1), keys(states2));
        close myclients(s, junk_, ?new_states);
      }
    } 
    producing_handle_predicate if(new_old == 0) basic_client_handle(ha, new_client, nil) else is_client(ha, new_old);
    @*/
    old = new_old;
    if(new_old == 0) {
      //@ close [f/2]stack(s, I);
      //@ close foreach(nil, two_thirds_data);
      //@ close stack_client(s, f/2, I, new_client); 
      return new_client;
    }
  }
}

void deactivate_client(struct stack* s, struct stack_client* client)
  //@ requires stack_client(s, ?f, ?I, client);
  //@ ensures [f]stack(s, I);
{; 
  //@ open stack_client(s, f, I, client);
  //@ assert [f]stack_box(?id, s, I);
  //@ assert basic_client_handle(?ha, id, client, ?retired);
  /*@
  consuming_box_predicate stack_box(id, s, I)
  consuming_handle_predicate basic_client_handle(ha, client, retired)
  perform_action set_hazard_pointer(client, 0)
  {
    open myclients(_, _, _);
    assert clients(?head_, 0, s, ?junk, ?states_);
    clients_split(head_, client);
    assert clients(head_, client, s, junk, ?states1_);
    assert clients(client, 0, s, junk, ?states2_);
    @*/ atomic_set_pointer(&client->hp, 0); /*@ 
    client->valid = false;
    clients_merge(head_, client);
    append_update_entry(client, (update_hp)(0), states1_, states2_); 
    assoc_update_entry(client, (update_hp)(0), states_);
      switch(assoc<struct stack_client*, client_state>(client, states_)) {
        case client_state(asdf, aqwer, ag, adg, myf):
      }
  } 
  producing_handle_predicate hazard_pointer_set(ha, client, retired, 0);
  @*/
  /*@
  consuming_box_predicate stack_box(id, s, I)
  consuming_handle_predicate hazard_pointer_set(ha, client, retired, 0)
  perform_action deactivate(client)
  {
    open myclients(_, _, _);
    assert clients(?head__, 0, s, _, ?states__);
    clients_split(head__, client);
    assert clients(head__, client, s, ?junk_, ?states1__);
    assert clients(client, 0, s, junk_, ?states2__);
    open clients(client, _, s, junk_, states2__);
    switch(assoc<struct stack_client*, client_state>(client, states1__)) {
      case client_state(a, b, c, d, e):
    }
    @*/ client->active = false; /*@ // todo: replace with atomic operation
    append_update_entry(client, (deactivate), states1__, states2__);
    assoc_update_entry(client, (deactivate), states__);
    assoc_append(client, states1__,  states2__);
    open client_local(client, s, _, _, junk_);
    foreach2foreachp(retired, two_thirds_data);
    clients_merge(head__, client);
  };
  @*/
  //@ close [f]stack(s, I);
}

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
    perform_action noop()
    {
      @*/ struct node* t = atomic_load_pointer(&s->top); /*@
    } 
    producing_handle_predicate basic_client_handle(ha, client, retired);
    @*/
    new_node->next = t;
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate basic_client_handle(ha, client, retired)
    perform_action push(new_node, data)
    {
      assert lseg(?hd, ?lst, ?nds, _);
      assert foreach(?junk, _);
      lseg_mem(hd, lst, new_node);
      junk_mem(junk, new_node);
      @*/ struct node* old = atomic_compare_and_set_pointer(&s->top, t, new_node); /*@
      if(old == t) {
        lem();
      }
    } 
    producing_handle_predicate basic_client_handle(ha, client, retired);
    @*/
    //@ close stack_client(s, f, I, client);
    if(old == t) {
      //@ leak is_stack_push_lemma(lem, I, data);
      return;
    }
  }
}

void phase1(struct stack* s, struct stack_client* client, struct list* plist)
  //@ requires [?f]stack_box(?id, s, ?I) &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& list(rlist, ?retired) &*& client->rcount |-> length(retired) &*& list(plist, nil) &*& basic_client_handle(ha, id, client, retired);
  //@ ensures [f]stack_box(id, s, I) &*& client->rlist |-> rlist &*& [1/2]client->myhandle |-> ha &*& list(rlist, retired) &*& client->rcount |-> length(retired) &*& list(plist, ?hazards) &*& phase2_handle(ha, id, client, retired, nil, retired, hazards);
{
  ;
  /*@
  consuming_box_predicate stack_box(id, s, I)
  consuming_handle_predicate basic_client_handle(ha, client, retired)
  perform_action noop()
  { 
    open myclients(_, _, _);
    open clients(_, _, s, _, ?client_states);
    @*/ struct stack_client* curr = atomic_load_pointer(&s->clients); /*@
    if(! forall(retired, (was_observed_or_no_validated_hps)(nil, values(take(0, client_states))))) {
      not_forall(retired, (was_observed_or_no_validated_hps)(nil, values(take(0, client_states))));
    }
  }
  producing_handle_predicate phase1_handle(ha, client, retired, curr, 0, true, nil);
  @*/
  //@ int i = 0;
  while(curr != 0) 
    /*@ invariant [f]stack_box(id, s, I) &*& 0 <= i &*& list(plist, ?hps) &*& 
                  curr != 0 ? phase1_handle(ha, id, client, retired, curr, i, true, hps) : phase2_handle(ha, id, client, retired, nil, retired, hps);
    @*/
  {
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate phase1_handle(ha, client, retired, curr, i, true, hps)
    perform_action noop()
    {
      open myclients(_, _, _);
      assert clients(?head, 0, s, _, ?states);
      assert foreach(?junk, _);
      assert i < length(states);
      clients_split(head, curr);
      assert clients(head, curr, s, junk, ?thestates1);
      assert clients(curr, 0, s, junk, ?thestates2);
      @*/ struct node* hp = atomic_load_pointer(&curr->hp); /*@
      list<struct node*> nhps = hp == 0 ? hps : cons(hp, hps);
      assert clients(curr, 0, s, junk, cons(pair(curr, client_state(hp, ?valid, ?curract, ?currha, ?myf)), ?rest));
      struct stack_client* currnext = curr->next;
      clients_merge(head, curr);
      clients_distinct(head, 0);
      nth_append_r(thestates1, thestates2, 0);
      distinct_keys_implies_distinct_entries(states);
      nth_index_of(i, states);
      nth_index_of(i, keys(states));
      nth_values(i, states);
      if(! forall(retired, (was_observed_or_no_validated_hps)(hp == 0 ? hps : cons(hp, hps), take(i + 1, values(states))))) {
        struct node* ex = not_forall(retired, (was_observed_or_no_validated_hps)(hp == 0 ? hps : cons(hp, hps), take(i + 1, values(states))));
        forall_elim(retired, (was_observed_or_no_validated_hps)(hps, take(i, values(states))), ex);
        if(mem(ex, nhps)) {
        } else {
          forall_elim(retired, (is_good_retired)(junk, client), ex);
          append_no_validated_hps(ex, take(i, values(states)), cons(nth(i, values(states)), nil));
          take_plus_one(i, values(states));
        }
      }
    }
    producing_handle_predicate phase1_handle(ha, client, retired, curr, i + 1, false, hp == 0 ? hps : cons(hp, hps));
    @*/
    if(hp != 0) {
      list_add_first(plist, hp);
    }
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate phase1_handle(ha, client, retired, curr, i + 1, false, hp == 0 ? hps : cons(hp, hps))
    perform_action noop()
    {
      open myclients(_, _, _);
      assert clients(?head_, _, s, ?junk_, ?states_);
      clients_split(head_, curr);
      assert clients(head_, curr, s, _, ?states1);
      assert clients(curr, 0, s, _, ?states2);
      struct stack_client* old_curr = curr;
      open clients(curr, 0, s, junk_, _);
      @*/ curr = atomic_load_pointer(&curr->next); /*@
      open clients(curr, 0, s, junk_, ?newstates2);
      clients_merge(head_, old_curr);
      clients_distinct(head_, 0);
      nth_index_of(i, keys(states_));
      append_keys(states1, states2);
      if(curr != 0) {
        nth_append_r(keys(states1),  keys(states2), 1);
      } else {
        take_length(values(states_));
      }
    }
    producing_handle_predicate if (curr != 0) phase1_handle(ha, client, retired, curr, i + 1, true, hp == 0 ? hps : cons(hp, hps)) else 
                                              phase2_handle(ha, client, retired, nil, retired, hp == 0 ? hps : cons(hp, hps));
    @*/
    //@ i++;
  }
}

/*@
lemma void clients_remove_junk(struct stack_client* c, struct stack_client* d, struct node* n)
  requires clients(c, 0, ?s, ?junk, ?states) &*& mem(pair(n, d), junk) == true &*& !mem(d, keys(states)) || is_active(assoc(d, states)) == true;
  ensures clients(c, 0, s, remove(pair(n, d), junk), states);
{
  clients_distinct(c, 0);
  open clients(c, 0, s, junk, states);
  if(c == 0) {
  } else {
    open client_local(c, s, ?active, ?myfrac, junk);
    if(! active) {
      assert list(_, ?retired);
      if(! forall(retired, (is_good_retired)(remove(pair(n, d), junk), c))) {
        struct node* ex = not_forall(retired, (is_good_retired)(remove(pair(n, d), junk), c));
        forall_elim(retired, (is_good_retired)(junk, c), ex);
        neq_mem_remove(pair(ex, c), pair(n, d), junk);
      }
      count_remove(junk, (has_owner)(c), pair(n, d));
    }
    clients_remove_junk(c->next, d, n);
  }
  close clients(c, 0, s, remove(pair(n, d), junk), states);
}

lemma void clients_add_junk(struct stack_client* c, struct stack_client* d, struct node* n)
  requires clients(c, 0, ?s, ?junk, ?states) &*&  !mem(d, keys(states)) || is_active(assoc(d, states)) == true;
  ensures clients(c, 0, s, cons(pair(n, d), junk), states);
{
  clients_distinct(c, 0);
  open clients(c, 0, s, junk, states);
  if(c == 0) {
  } else {
    open client_local(c, s, ?active, ?myfrac, junk);
    if(! active) {
      assert list(_, ?retired);
      if(! forall(retired, (is_good_retired)(cons(pair(n, d), junk), c))) {
        struct node* ex = not_forall(retired, (is_good_retired)(cons(pair(n, d), junk), c));
        forall_elim(retired, (is_good_retired)(junk, c), ex);
      }
    }
    clients_add_junk(c->next, d, n);
  }
  close clients(c, 0, s, cons(pair(n, d), junk), states);
}

fixpoint bool not_contains<t>(list<t> xs, t x) {
  return ! mem(x, xs); 
}

lemma void not_contains_remove_project_nodes(list<pair<struct node*, struct stack_client*> > junk, struct node* n, struct stack_client* c, struct node* nn)
  requires ! mem(nn, keys(junk));
  ensures ! mem(nn, keys(remove(pair(n, c), junk)));
{
  switch(junk) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(n0, c0):
          if(n0 == n && c0 == c) {
          } else {
            not_contains_remove_project_nodes(t, n, c, nn);
          }
      }
  }
}
@*/

void phase2(struct stack* s, struct stack_client* client, struct list* plist)
  //@ requires [?f]stack_box(?id, s, ?I) &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& list(rlist, ?retired) &*& distinct(retired) == true &*& client->rcount |-> length(retired) &*& list(plist, ?hazards) &*& phase2_handle(ha, id, client, retired, nil, retired, hazards) &*& foreach(retired, two_thirds_data);
  //@ ensures [f]stack_box(id, s, I) &*& client->rlist |-> rlist &*& [1/2]client->myhandle |-> ha &*& list(rlist, ?retired2)  &*& distinct(retired2) == true &*& client->rcount |-> length(retired2) &*& list(plist, hazards) &*& basic_client_handle(ha, id, client, retired2) &*& foreach(retired2, two_thirds_data);
{
  struct list* tmplist = list_remove_all(client->rlist);
  client->rcount = 0;
  //@ close foreach(nil, two_thirds_data);
  /*@
  if(! forall(retired, (not_contains)(nil))) {
    struct node* n = not_forall(retired, (not_contains)(nil));
  }
  @*/
  while(! list_is_empty(tmplist))
    /*@ invariant [f]stack_box(id, s, I) &*& client->rlist |-> rlist &*& list(rlist, ?newretired) &*& client->rcount |-> length(newretired) &*& 
                  list(tmplist, ?todos) &*& list(plist, hazards) &*& [1/2]client->myhandle |-> ha &*& phase2_handle(ha, id, client, append(newretired, todos), newretired, todos, hazards) &*&
                  foreach(newretired, two_thirds_data) &*& foreach(todos, two_thirds_data) &*& distinct(newretired) == true &*& distinct(todos) == true &*&
                  forall(todos, (not_contains)(newretired)) == true;
                   @*/
    //@ decreases length(todos);
  {
    struct node* curr = list_remove_first(tmplist);
    if(list_contains(plist, curr)) {
      list_add_first(client->rlist, curr);
      if(client->rcount == INT_MAX)
        abort();
      client->rcount++;
      //@ open foreach(todos, two_thirds_data);
      //@ close foreach(cons(head(todos), newretired), two_thirds_data);
      /*@
      consuming_box_predicate stack_box(id, s, I)
      consuming_handle_predicate phase2_handle(ha, client, append(newretired, todos), newretired, todos, hazards)
      perform_action noop()
      {
        assert foreach(?junk, _);
        if(! forall(append(cons(curr, newretired), tail(todos)), (is_good_retired)(junk, client))) {
          struct node* ex = not_forall(append(cons(curr, newretired), tail(todos)), (is_good_retired)(junk, client));
          forall_elim(append(newretired, todos), (is_good_retired)(junk, client), ex);
        }
      }
      producing_handle_predicate phase2_handle(ha, client, append(cons(curr, newretired), tail(todos)), cons(curr, newretired), tail(todos), hazards);
      @*/
      /*@
      if(! forall(tail(todos), (not_contains)(cons(curr, newretired)))) {
        struct node* ex = not_forall(tail(todos), (not_contains)(cons(curr, newretired)));
        forall_elim(todos, (not_contains)(newretired), ex);
      }
      @*/
    } else {
      /*@
      consuming_box_predicate stack_box(id, s, I)
      consuming_handle_predicate phase2_handle(ha, client, append(newretired, todos), newretired, todos, hazards)
      perform_action release_node(client, curr)
      {
        open myclients(_, _, _);
        assert clients(?firstclient, _, s, ?junk, ?client_states);
        assert foreach(junk, _);
        assert lseg(_, _, ?nodes, _);
        switch(todos) { case nil: case cons(currr, rest): }
        forall_elim(todos, (was_observed_or_no_validated_hps)(hazards, values(client_states)), curr);
        
        foreach_remove(pair(curr, client), junk);
        if(! forall(newretired, (is_good_retired)(remove(pair(curr, client), junk), client))) {
          struct node* ex = not_forall(newretired, (is_good_retired)(remove(pair(curr, client), junk), client));
          forall_elim(append(newretired, todos), (is_good_retired)(junk, client), ex);
          neq_mem_remove(pair(ex, client), pair(curr, client), junk);
        }
        
        if(! forall(tail(todos), (is_good_retired)(remove(pair(curr, client), junk), client))) {
           struct node* ex = not_forall(tail(todos), (is_good_retired)(remove(pair(curr, client), junk), client));
           forall_elim(todos, (is_good_retired)(junk, client), ex);
           neq_mem_remove(pair(ex, client), pair(curr, client), junk);
        }
        if(! forall(nodes, (not_contains)(keys(remove(pair(curr, client), junk))))) {
           struct node* ex = not_forall(nodes, (not_contains)(keys(remove(pair(curr, client), junk))));
           forall_elim(nodes, (not_contains)(keys(junk)), ex);
           not_contains_remove_project_nodes(junk, curr, client, ex);
        }
        if(! forall(remove(pair(curr, client), junk), (is_good_junk)(keys(client_states)))) {
           pair<struct node*, struct stack_client*> ex = not_forall(remove(pair(curr, client), junk), (is_good_junk)(keys(client_states)));
           neq_mem_remove(ex, pair(curr, client), junk);
           forall_elim(junk, (is_good_junk)(keys(client_states)), ex);
        }
        junk_mem_remove(junk, curr, client);
        distinct_remove(curr, keys(junk));
        clients_remove_junk(firstclient, client, curr);
        count_remove(junk, (has_owner)(client), pair(curr, client));
        if(! forall(append(newretired, tail(todos)), (is_good_retired)(remove(pair(curr, client), junk), client))) {
          struct node* ex = not_forall(append(newretired, tail(todos)), (is_good_retired)(remove(pair(curr, client), junk), client));
          forall_elim(append(newretired, todos), (is_good_retired)(junk, client), ex);
          neq_mem_remove(pair(ex, client), pair(curr, client), junk);
        }
      }
      producing_handle_predicate phase2_handle(ha, client, append(newretired, tail(todos)), newretired, tail(todos), hazards);
      @*/
      //@ foreach_remove(curr, todos);
      //@ open two_thirds_data(curr);
      //@ open is_node(_);
      free(curr);
    }
   
  }
  list_dispose(tmplist);
  /*@
  consuming_box_predicate stack_box(id, s, I)
  consuming_handle_predicate phase2_handle(ha, client, append(newretired, nil), newretired, nil, hazards)
  perform_action noop()
  {
    
  }
  producing_handle_predicate basic_client_handle(ha, client, newretired);
  @*/
  //@ open foreach(todos, two_thirds_data);
}


void retire_node(struct stack* s, struct stack_client* client, struct node* n)
  //@ requires [?f]stack_box(?id, s, ?I) &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& list(rlist, ?retired) &*& client->rcount |-> length(retired) &*& distinct(retired) == true &*& basic_client_handle(ha, id, client, cons(n, retired)) &*& n != 0 &*& [2/3]n->data |-> ?data &*& foreach(retired, two_thirds_data);
  //@ ensures [f]stack_box(id, s, I) &*& client->rlist |-> rlist &*& [1/2]client->myhandle |-> ha &*& list(rlist, ?retired2) &*& client->rcount |-> length(retired2)  &*& distinct(retired2) == true &*& basic_client_handle(ha, id, client, retired2) &*& foreach(retired2, two_thirds_data);
{
  list_add_first(client->rlist, n);
  //@ foreach_two_thirds_mem(retired, n);
  //@ close foreach(cons(n, retired), two_thirds_data);
  if(client->rcount == INT_MAX)
    abort();
  client->rcount++;
  int R = 10;
  if(client->rcount > R) {
    struct list* plist = create_list();
    phase1(s, client, plist);
    phase2(s, client, plist);
    list_dispose(plist);
  }
}



bool stack_pop(struct stack* s, struct stack_client* client, void** out)
  //@ requires stack_client(s, ?f, ?I, client) &*& *out |-> _ &*& is_stack_pop_lemma(?lem, I) &*& stack_pop_pre(lem)();
  //@ ensures stack_client(s, f, I, client) &*& stack_pop_post(lem)(result, ?pst) &*& result ? *out |-> pst : *out |-> _;
{
  struct node* t, n, tmp, old;
  void* data;
  while(true)
    //@ invariant stack_client(s, f, I, client) &*& *out |-> _ &*& is_stack_pop_lemma(lem, I) &*& stack_pop_pre(lem)();
  {
    //@ open stack_client(s, f, I, client);
    /*@
    consuming_box_predicate stack_box(?id, s, I)
    consuming_handle_predicate basic_client_handle(?ha, client, ?retired)
    perform_action noop()
    {
      @*/ t = atomic_load_pointer(&s->top); /*@
      if(t == 0) {
        open lseg(_, _, _, _);
        lem();
      }
    } 
    producing_handle_predicate basic_client_handle(ha, client, retired);
    @*/
    if(t == 0) {
      //@ close stack_client(s, f, I, client);
      //@ leak is_stack_pop_lemma(lem, I);
      return false;
    }
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate basic_client_handle(ha, client, retired)
    perform_action set_hazard_pointer(client, t)
    {
      open myclients(_, _, ?states);
      assert clients(?head, 0, s, ?junk0, states);
      clients_split(head, client);
      assert clients(head, client, s, junk0, ?states1); 
      open clients(client, 0, s, junk0, ?states2);
      @*/ atomic_set_pointer(&client->hp, t); /*@
      client->valid = false;
      clients_merge(head, client);
      append_update_entry(client, (update_hp)(t), states1, states2); 
      assoc_update_entry(client, (update_hp)(t), states);
      switch(assoc<struct stack_client*, client_state>(client, states)) {
        case client_state(asdf, aqwer, ag, adg, myf):
      }
    } 
    producing_handle_predicate hazard_pointer_set(ha, client, retired, t);
    @*/
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate hazard_pointer_set(ha, client, retired, t)
    perform_action validate_hazard_pointer(client)
    {
      open lseg(_, _, _, _);
      @*/ tmp = atomic_load_pointer(&s->top); /*@
      if(tmp == t) {
        open myclients(_, ?junk_, ?states_);
        assert clients(?head_, 0, s, junk_, states_);
        clients_split(head_, client);
        assert clients(head_, client, s, junk_, ?states1_);
        assert clients(client, 0, s, junk_, ?states2_);
        client->valid = true;
        assert client->active |-> true;
        clients_merge(head_, client);
        assert clients(head_, 0, s, junk_, ?poststates_);
        append_update_entry(client, (validate_hp), states1_, states2_);
        assoc_update_entry(client, (validate_hp), states_);
        assoc_append(client, states1_,  states2_);
      }
    } 
    producing_handle_predicate if (tmp == t) was_top(ha, client, retired, t) else basic_client_handle(ha, client, retired);
    @*/
    if(tmp != t) {
      //@ close stack_client(s, f, I, client);
    } else {
      /*@
      consuming_box_predicate stack_box(id, s, I)
      consuming_handle_predicate was_top(ha, client, retired, t)
      perform_action noop()
      {
        assert s->top |-> ?top;
        assert foreach(?junk, is_node);
        assert lseg(top, 0, ?nodes, ?vs);
        if(mem(t, keys(junk))) {
          junk_remove(junk, t);
        } else {
          lseg_split(top, 0, t);
        }
        @*/ n = atomic_load_pointer(&t->next); /*@
        close node_next(t, _);
        if(mem(t, keys(junk))) {
          lseg_mem(top, 0, t);
          assert t->owner |-> ?owner;
          close is_node(pair(t, owner));
          junk_unremove(junk, t);
        } else {
          open lseg(n, _, _, _);
          lseg_mem(top, t, t);
          if(n != 0) {
            lseg_mem(top, t, n);
          } else {
            lseg_mem_zero(top, t);
          }
          lseg_merge(top, t);
        }
      }
      producing_handle_predicate was_top_with_next(ha, client, retired, t, n);
      @*/
      /*@
      consuming_box_predicate stack_box(id, s, I)
      consuming_handle_predicate was_top_with_next(ha, client, retired, t, n)
      perform_action pop(client)
      {
        open lseg(_, _, ?thenodes, _);
        open myclients(s, ?thejunk, _);
        assert clients(?firstclient, _, s, thejunk, ?states__);
        assert foreach(thejunk, _);
        @*/ old = atomic_compare_and_set_pointer(&s->top, t, n); /*@
        close stack_top(s, _);
        if(old == t) {
          assert foreach(?junk_, is_node);
          open lseg(_, _, _, _);
          t->owner = client;
          close foreach(cons(pair(t, client), junk_), is_node);
          lem();
          if(! forall(retired, (is_good_retired)(cons(pair(t, client), junk_), client))){
            struct node* ex = not_forall(retired, (is_good_retired)(cons(pair(t, client), junk_), client));
            forall_elim(retired, (is_good_retired)(junk_, client), ex);
          }
          if(!forall(tail(thenodes), (not_contains)(keys(cons(pair(t, client), junk_))))){
            struct node* ex = not_forall(tail(thenodes), (not_contains)(keys(cons(pair(t, client), junk_))));
            forall_elim(thenodes, (not_contains)(keys(junk_)), ex);
          }
          clients_add_junk(firstclient, client, t);
        }
      }
      producing_handle_predicate if(old == t) basic_client_handle(ha, client, cons(t, retired)) else basic_client_handle(ha, client, retired);
      @*/
      if(old == t) {
        /*@
        consuming_box_predicate stack_box(id, s, I)
        consuming_handle_predicate basic_client_handle(ha, client, cons(t, retired))
        perform_action noop()
        {
          assert foreach(?junk__, _);
          foreach_remove(pair(t, client), junk__);
          @*/ data = atomic_load_pointer(&t->data); /*@
          foreach_unremove(pair(t, client), junk__);
        }
        producing_handle_predicate basic_client_handle(ha, client, cons(t, retired));
        @*/
        retire_node(s, client, t);
        //@ close stack_client(s, f, I, client);
        //@ leak is_stack_pop_lemma(lem, I);
        *out = data;
        return true;
      } else {
        //@ close stack_client(s, f, I, client);
      }
    }
  }
}

void stack_dipose(struct stack* s)
  //@ requires stack(s, ?I);
  //@ ensures I(?vs);
{
  //@ open stack(s, I);
  //@ assert stack_box(?id, s, I);
  //@ dispose_box stack_box(id, s, I);
  //@ open myclients(s, ?junk0, ?states0);
  struct stack_client* curr = s->clients;
  while(curr != 0)
    //@ invariant clients(curr, 0, s, ?junk, ?states) &*& s->help |-> _ &*& foreach(junk, is_node) &*& forall(junk, (is_good_junk)(keys(states))) == true;
  {
    //@ clients_distinct(curr, 0);
    struct stack_client* nxt = curr->next;
    //@ assert clients(nxt, 0, s, junk, ?nstates);
    //@ open client_local(curr, s, _, _, junk);
    //@ assert [1/2]curr->active |-> ?active;
    struct list* retired = curr->rlist;
    //@ assert list(retired, ?nodes0);
    while(!list_is_empty(retired))
      /*@ invariant list(retired, ?nodes) &*& foreachp(nodes, two_thirds_data) &*& foreach(?junk_, is_node) &*&
                    forall(nodes, (is_good_retired)(junk_, curr)) == true &*& distinct(nodes) == true &*&
                    forall(junk_, (is_good_junk)(keys(states))) == true &*& clients(nxt, 0, s, junk_, nstates) &*&
                    count(junk_, (has_owner)(curr)) == length(nodes); @*/
    {
      //@ switch(nodes) { case nil: case cons(h, t): }
      struct node* n = list_remove_first(retired);
      //@ foreach_remove(pair(n, curr), junk_);
      //@ foreachp_remove(n, nodes);
      free(n);
      //@ clients_remove_junk(nxt, curr, n);
      /*@
      if(! forall(tail(nodes), (is_good_retired)(remove(pair(n, curr), junk_), curr))) {
         struct node* ex = not_forall(tail(nodes), (is_good_retired)(remove(pair(n, curr), junk_), curr));
         forall_elim(nodes, (is_good_retired)(junk_, curr), ex);
         neq_mem_remove(pair(ex, curr), pair(n, curr), junk_);
      } 
      @*/
      /*@
      if( ! forall(remove(pair(n, curr), junk_), (is_good_junk)(keys(states)))) {
        pair<struct node*, struct stack_client*> ex = not_forall(remove(pair(n, curr), junk_), (is_good_junk)(keys(states)));
        mem_remove_mem(ex, pair(n, curr), junk_);
        forall_elim(junk_, (is_good_junk)(keys(states)), ex);
      } 
      @*/
      //@ count_remove(junk_, (has_owner)(curr), pair(n, curr));
    }
    /*@
    if(! forall(junk_, (is_good_junk)(keys(tail(states))))) {
      pair<struct node*, struct stack_client*> ex = not_forall(junk_, (is_good_junk)(keys(tail(states))));
      forall_elim(junk_, (is_good_junk)(keys(states)), ex);
      count_zero_mem(junk_, (has_owner)(curr), ex);
    }
    @*/
    list_dispose(retired);
    free(curr);
    curr = nxt;
  }
  struct node* n = s->top;
  while(n != 0)
    //@ invariant lseg(n, 0, _, _);
  {
    struct node* nxt = n->next;
    free(n);
    n = nxt;
  }
  //@ open clients(0, 0, s, _, _);
  //@ open lseg(0, 0, _, _);
  //@ switch(junk) { case nil: case cons(h,t): }
  //@ open foreach(_, is_node);
  free(s);
}

