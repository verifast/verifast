#include "atomics.h"
#include "stdlib.h"
//@ #include "quantifiers.gh"
//@ #include "listex.gh"

/*@
lemma_auto(mem(x, append(xs, ys))) void mem_append<t>(list<t> xs, list<t> ys, t x)
  requires true;
  ensures mem(x, append(xs, ys)) == (mem(x, xs) || mem(x, ys));
{
  switch(xs) {
    case nil:
    case cons(h, t): mem_append(t, ys, x);
  }
}
lemma_auto(index_of(x, append(xs, ys))) void index_of_append<t>(list<t> xs, list<t> ys, t x)
  requires mem(x, xs) == true;
  ensures index_of(x, xs) == index_of(x, append(xs, ys));
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(x != h) 
        index_of_append(t, ys, x);
  }
}

lemma_auto(index_of(x, append(xs, ys))) void index_of_append2<t>(list<t> xs, list<t> ys, t x)
  requires mem(x, ys) == true && !mem(x, xs);
  ensures length(xs) + index_of(x, ys) == index_of(x, append(xs, ys));
{
  switch(xs) {
    case nil:
    case cons(h, t):
        index_of_append2(t, ys, x);
  }
}

lemma_auto(nth(i, append(xs, ys))) void nth_append_auto<t>(list<t> xs, list<t> ys, int i)
  requires 0 <= i && i < length(xs);
  ensures nth(i, xs) == nth(i, append(xs, ys));
{
  nth_append(xs, ys, i);
}

lemma_auto(nth(i, append(xs, ys))) void nth_append2<t>(list<t> xs, list<t> ys, int i)
  requires 0 <= i && i < length(ys);
  ensures nth(i, ys) == nth(length(xs) + i, append(xs, ys));
{
  switch(xs) {
    case nil:
    case cons(h, t):
        nth_append2(t, ys, i);
  }
}

lemma void nth_index_of<t>(int i, list<t> xs)
  requires distinct(xs) == true &*& 0 <= i && i < length(xs);
  ensures index_of(nth(i, xs), xs) == i;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i != 0) {
      nth_index_of(i - 1, t);
      }
  }
}
@*/

/*
TODO:
  - add actions for adding and removing clients
  - take into account the 'active' bit
  - specify that junk nodes are owned by active clients (needed to dispose a stack)
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

lemma_auto void length_project_stack_clients(list<client_state> states)
  requires true;
  ensures length(states) == length(project_stack_clients(states));
{
    switch(states) {
    case nil: 
    case cons(h, nstates):
       switch(h) {
         case client_state(client, hp, valid, active, ha):  length_project_stack_clients(nstates);
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

lemma void update_hp_preserves_is_valid(struct stack_client* c, struct stack_client* client, struct node* n, list<client_state> states) 
  requires client != c;
  ensures is_valid(c, states) == is_valid(c, update_hp(client, n, states));
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
          if(client == client0) {
          } else {
             update_hp_preserves_is_valid(c, client, n, nstates);
          }
      }
  }
}

lemma void update_hp_preserves_no_validated_hps(struct node* nn, struct stack_client* client, struct node* n, list<client_state> states) 
  requires no_validated_hps(nn, states) == true ;
  ensures no_validated_hps(nn, update_hp(client, n, states)) == true;
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
           update_hp_preserves_no_validated_hps(nn, client, n, nstates);
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

lemma void validate_hp_preserves_is_valid(struct stack_client* c, struct stack_client* client, list<client_state> states) 
  requires client != c;
  ensures is_valid(c, states) == is_valid(c, validate_hp(client, states));
{
  switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
          if(client == client0) {
          } else {
            validate_hp_preserves_is_valid(c, client, nstates);
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

lemma void validate_different_hp_preserves_no_validated_hps(struct node* n, struct stack_client* client, list<client_state> states) 
  requires n != get_hp(client, states) || ! mem(client, project_stack_clients(states));
  ensures no_validated_hps(n, states) == no_validated_hps(n, validate_hp(client, states));
{
    switch(states) {
    case nil:
    case cons(h, nstates):
      switch(h) {
        case client_state(client0, hp, valid, active, ha): 
          if(client == client0) {
          } else {
            validate_different_hp_preserves_no_validated_hps(n, client, nstates);
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

fixpoint bool is_valid(struct stack_client* client,  list<client_state> states) {
    switch(states) {
    case nil: return false;
    case cons(h, nstates):
      return switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          return client == client0 ?
            valid0
          :
            is_valid(client, nstates);
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

lemma void append_no_validated_hps(struct node* n, list<client_state> states1, list<client_state> states2)
  requires no_validated_hps(n, states1) == true &*& no_validated_hps(n, states2) == true;
  ensures no_validated_hps(n, append(states1, states2)) == true;
{
  switch(states1) {
    case nil:
    case cons(h, t):
      switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
        append_no_validated_hps(n, t, states2);
      }
  }
}


fixpoint bool was_observed_or_no_validated_hps(list<struct node*> observedhazards, list<client_state> states, struct node* node) {
  return mem(node, observedhazards) || no_validated_hps(node, states);
}

fixpoint bool is_good_retired(list<pair<struct node*, struct stack_client*> > junk, struct stack_client* owner, struct node* retired)
{
  return retired != 0 && mem(pair(retired, owner), junk);
}
@*/

/*@
predicate clients(struct stack_client* client, struct stack_client* client2; list<client_state> client_states) =
  client == client2 ?
    client_states == nil
  :
    client != 0 &*& client->hp |-> ?hp &*& client->active |-> ?active &*& [1/2]client->myhandle |-> ?ha &*& client->valid |-> ?valid &*& client->next |-> ?next &*& clients(next, client2, ?nclient_states) &*& 
    client_states == cons(client_state(client, hp, valid, active, ha), nclient_states);

lemma void clients_mem(struct stack_client* c1, struct stack_client* c2, struct stack_client* c3)
  requires clients(c1, c2, ?states) &*& c3->hp |-> ?hp;
  ensures clients(c1, c2, states) &*& c3->hp |-> hp &*& ! mem(c3, project_stack_clients(states));
{
  open clients(c1, c2, states);
  if(c1 != c2) {
    clients_mem(c1->next, c2, c3);
  }
}

lemma void clients_distinct(struct stack_client* c1, struct stack_client* c2)
  requires clients(c1, c2, ?states);
  ensures clients(c1, c2, states) &*& distinct(project_stack_clients(states)) == true;
{
  open clients(c1, c2, states);
  if(c1 == c2) {
  } else {
    clients_mem(c1->next, c2, c1);
    clients_distinct(c1->next, c2);
  }
}

lemma void clients_split(struct stack_client* client, struct stack_client* curr) 
  requires clients(client, 0, ?states) &*& mem(curr, project_stack_clients(states)) == true;
  ensures clients(client, curr, ?states1) &*& clients(curr, 0, ?states2) &*& states == append(states1, states2) && 
          length(states1) == index_of(curr, project_stack_clients(states)) &&
          ! mem(curr, project_stack_clients(states1));
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
  ensures lseg(a, 0, append(ns1, ns2), append(vs1, vs2));
{
  open lseg(a, b, ns1, vs1);
  if(a != b) {
    lseg_merge(a->next, b);
  }
}

fixpoint list<struct node*> project_nodes(list<pair<struct node*, struct stack_client*> > junk) {
  switch(junk) {
    case nil: return nil;
    case cons(h, t): return cons(fst(h), project_nodes(t));
  }
}

lemma void mem_project_nodes(list<pair<struct node*, struct stack_client*> > junk, struct node* n, struct stack_client* c)
  requires mem(pair(n, c), junk) == true;
  ensures mem(n, project_nodes(junk)) == true;
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

lemma void not_mem_project_nodes(list<pair<struct node*, struct stack_client*> > junk, struct node* n, struct stack_client* c)
  requires ! mem(n, project_nodes(junk));
  ensures ! mem(pair(n, c), junk);
{
  switch(junk) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(n0, c0):
          if(n0 == n && c0 == c) {
          } else {
            not_mem_project_nodes(t, n, c);
          }
      }
  }
}

lemma void junk_mem(list<pair<struct node*, struct stack_client* > > junk, struct node* n)
  requires foreach(junk, is_node) &*& n->next |-> ?nxt;
  ensures foreach(junk, is_node) &*& n->next |-> nxt &*& ! mem(n, project_nodes(junk));
{
  switch(junk) {
    case nil:
    case cons(h, t):
      open foreach(junk, is_node);
      open is_node(h);
      junk_mem(t, n);
      close is_node(h);
      close foreach(junk, is_node);
  }
}

lemma void junk_mem_remove(list<pair<struct node*, struct stack_client* > > junk, struct node* n, struct stack_client* c)
  requires mem(pair(n, c), junk) == true &*& distinct(project_nodes(junk)) == true;
  ensures project_nodes(remove(pair(n, c), junk)) == remove(n, project_nodes(junk)); 
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
              not_mem_project_nodes(t, n, c);
            } else {
            }
          }
      }
  } 
}

predicate is_node(pair<struct node*, struct stack_client*> p) = 
  switch(p) {
    case pair(n, client): return n != 0 &*& n->next |-> _ &*& [1/3]n->data |-> _ &*& n->owner |-> client &*& malloc_block_node(n);
  };
  
lemma void invalidated_hps_lemma(list<client_state> states, struct stack_client* client) 
  requires mem(client, project_stack_clients(states)) == true &*& is_valid(client, states) == true;
  ensures ! no_validated_hps(get_hp(client, states), states);
{
  switch(states) {
    case nil:
    case cons(h, t):
      switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          if(client0 == client) {
          } else {
            invalidated_hps_lemma(t, client);
          }
      }
  }
}

lemma void take_update_hp(struct stack_client* cl, struct node* n, list<client_state> states, int i)
  requires 0 <=i &*& i <= length(states);
  ensures update_hp(cl, n, take(i, states)) == take(i, update_hp(cl, n, states));
{
  switch(states) {
    case nil:
    case cons(h, t):
      switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          if(client0 == cl) {
          } else {
            if(i == 0) {
            } else {
              take_update_hp(cl, n, t, i - 1);
            }
          }
      }
  }
}

lemma void take_validate_hp(struct stack_client* cl, list<client_state> states, int i)
  requires 0 <=i &*& i <= length(states);
  ensures validate_hp(cl, take(i, states)) == take(i, validate_hp(cl, states));
{
  switch(states) {
    case nil:
    case cons(h, t):
      switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          if(client0 == cl) {
          } else {
            if(i == 0) {
            } else {
              take_validate_hp(cl, t, i - 1);
            }
          }
      }
  }
}

lemma void take_mem_project(list<client_state> states, struct stack_client* c, int index)
  requires 0 <= index && index <= length(states) &*& mem(c, project_stack_clients(take(index, states))) == true;
  ensures get_hp(c, take(index, states)) == get_hp(c, states);
{
  switch(states) {
    case nil:
    case cons(h, t):
     switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          if(client0 == c) {
          } else {
            if(index == 0) {
            } else {
              take_mem_project(t, c, index - 1);
            }
          }
      }
  }
  
}

box_class stack_box(struct stack* s, predicate(list<void*>) I) {
  invariant s->top |-> ?top &*& lseg(top, 0, ?nodes, ?vs) &*& 
            myclients(s, ?client_states) &*& foreach(?junk, is_node) &*& I(vs) &*&
            // derived info
            (top == 0 ? nodes == nil : nodes != nil && head(nodes) == top) &*&
            distinct(nodes) == true &*&
            forall(nodes, (not_contains)(project_nodes(junk))) == true &*&
            distinct(project_nodes(junk)) == true;
  
  action noop();
    requires true;
    ensures (top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk);
  
  action push(struct node* new_node, void* v);
    requires !mem(new_node, nodes) && ! mem(new_node, project_nodes(junk));
    ensures (top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk) 
            ||
            (top == new_node && nodes == cons(new_node, old_nodes) && vs == cons(v, old_vs) && client_states == old_client_states && junk == old_junk);
  
  action pop(struct stack_client* client);
    requires actionHandle == get_handle(client, client_states);
    ensures (top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk) 
            ||
            (old_nodes != nil && top == (nodes == nil ? (void*) 0 : nth(0, nodes)) && nodes == tail(old_nodes) && vs == tail(old_vs) && client_states == old_client_states && junk == cons(pair(old_top, client), old_junk));
  
  action set_hazard_pointer(struct stack_client* client, struct node* n);
    requires mem(client, project_stack_clients(client_states)) == true && actionHandle == get_handle(client, client_states);
    ensures (top == old_top && nodes ==old_nodes && vs == old_vs && client_states == update_hp(client, n, old_client_states) && junk == old_junk);
  
  action validate_hazard_pointer(struct stack_client* client);
    requires mem(client, project_stack_clients(client_states)) == true && actionHandle == get_handle(client, client_states);
    ensures (get_hp(client, old_client_states) != old_top && top == old_top && nodes == old_nodes && vs == old_vs && client_states == old_client_states && junk == old_junk) 
            ||
            (get_hp(client, old_client_states) == old_top && old_top != 0 && top == old_top && nodes == old_nodes && vs == old_vs && client_states == validate_hp(client, old_client_states) && junk == old_junk);
  
  action release_node(struct stack_client* client, struct node* n);
    requires mem(client, project_stack_clients(client_states)) && mem(pair(n, client), junk) && actionHandle == get_handle(client, client_states) &&
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
          neq_mem_remove( pair(n, client), pair(action_n, action_client), old_junk);
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
          neq_mem_remove(pair(n, client), pair(action_n, action_client), old_junk);
        }
      }
    }
  }
  
  handle_predicate was_top(struct stack_client* client, list<struct node*> retired, bool success, struct node* t) {
    invariant mem(client,  project_stack_clients(client_states)) == true &&
              forall(retired, (is_good_retired)(junk, client)) && 
              get_handle(client, client_states) == predicateHandle &&
              (!success || t != 0) &&
              (! success || (get_hp(client, client_states) == t && is_valid(client, client_states))) &&
              (!success || mem(t, nodes) || mem(t, project_nodes(junk)));
              
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      switch(old_nodes) {
        case nil:
        case cons(hh, tt):
      }
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
      update_hp_preserves_is_valid(client, action_client, action_n, old_client_states);
    }
    
    preserved_by validate_hazard_pointer(action_client) {
      validate_hp_preserves_clients(action_client, old_client_states);
      validate_hp_preserves_hps(client, action_client, old_client_states);
      validate_hp_preserves_length(action_client, old_client_states);
      validate_hp_preserves_handles(client, action_client, old_client_states);
      validate_hp_preserves_is_valid(client, action_client, old_client_states);
    }
    
    preserved_by release_node(action_client, action_n) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
        if(pair(action_n, action_client) != pair(n, client)) {
          neq_mem_remove(pair(n, client), pair(action_n, action_client), old_junk);
        }
      }
      if(!success) {
      } else {
        if(mem(t, old_nodes)) {
        } else {
          if(action_n != t) {
            junk_mem_remove(old_junk, action_n, action_client);
            neq_mem_remove(t, action_n, project_nodes(old_junk));
          } else {
            invalidated_hps_lemma(old_client_states, client);
          }
        }
      }
    }
  }
  
  handle_predicate is_junk(struct stack_client* client, list<struct node*> retired, bool success, struct node* t) {
    invariant mem(client,  project_stack_clients(client_states)) == true &&
              forall(retired, (is_good_retired)(junk, client)) && 
              get_handle(client, client_states) == predicateHandle &&
              (! success || mem(pair(t, client), junk));
              
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
          neq_mem_remove(pair(n, client), pair(action_n, action_client), old_junk);
        }
      }
      if(success) {
        neq_mem_remove(pair(t, client), pair(action_n, action_client), old_junk);
      }
    }
  }
  
  handle_predicate was_top_with_next(struct stack_client* client, list<struct node*> retired, struct node* t, struct node* tn) {
    invariant mem(client,  project_stack_clients(client_states)) == true &&
              forall(retired, (is_good_retired)(junk, client)) && 
              get_handle(client, client_states) == predicateHandle &&
              get_hp(client, client_states) == t && is_valid(client, client_states) &&
              t != 0 &&
              (mem(t, nodes) ?
                (tn != 0 ? 
                  mem(tn, nodes) && index_of(tn, nodes) == index_of(t, nodes) + 1
                :
                  index_of(t, nodes) == length(nodes) - 1
                )
                :
                  mem(t, project_nodes(junk))
              );
              
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      if(! forall(retired, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(retired, (is_good_retired)(junk, client));
        forall_elim(retired, (is_good_retired)(old_junk, client), n);
      }
      switch(old_nodes) {
        case nil:
        case cons(hh, tt):
      }
    }
    preserved_by set_hazard_pointer(action_client, action_n) {
      update_hp_preserves_clients(action_client, action_n, old_client_states);
      update_hp_preserves_other_hps(client, action_client, action_n, old_client_states);
      update_hp_preserves_length(action_client, action_n, old_client_states);
      update_hp_preserves_handles(client, action_client, action_n, old_client_states);
      update_hp_preserves_is_valid(client, action_client, action_n, old_client_states);
    }
    preserved_by validate_hazard_pointer(action_client) {
      validate_hp_preserves_clients(action_client, old_client_states);
      validate_hp_preserves_hps(client, action_client, old_client_states);
      validate_hp_preserves_length(action_client, old_client_states);
      validate_hp_preserves_handles(client, action_client, old_client_states);
      validate_hp_preserves_is_valid(client, action_client, old_client_states);
    }
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
          neq_mem_remove(t, action_n, project_nodes(old_junk));
        } else {
          invalidated_hps_lemma(old_client_states, client);
        }
      }
    }
  }
  
  handle_predicate phase1_handle(struct stack_client* client, list<struct node*> retired, struct stack_client* curr, int index, bool curratindex, list<struct node*> observedhps, bool phase2) {
    invariant mem(client,  project_stack_clients(client_states)) == true &&
              forall(retired, (is_good_retired)(junk, client)) && 
              get_handle(client, client_states) == predicateHandle &&
              0 <= index && index <= length(client_states) &&
              (!phase2 ?
                (curr != 0 ? 
                 mem(curr,  project_stack_clients(client_states)) == true &&
                 (curratindex ?
                     index < length(client_states) && 
                     nth(index,  project_stack_clients(client_states)) == curr
                   :
                     nth(index - 1,  project_stack_clients(client_states)) == curr
                 )
                : 
                  true) &&
                forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, client_states)))
              :
                forall(retired, (was_observed_or_no_validated_hps)(observedhps, client_states))
              );
                
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
      update_hp_preserves_is_valid(client, action_client, action_n, old_client_states);
      if(!phase2) {
        if(!forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, client_states)))) {
          struct node* ex = not_forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, client_states)));
          forall_elim(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, old_client_states)), ex);
          if(!mem(ex, observedhps)) {
            update_hp_preserves_no_validated_hps(ex, action_client, action_n, take(index, old_client_states)); 
            take_update_hp(action_client, action_n, old_client_states, index);
          }
        }
      } else {
        if(!forall(retired, (was_observed_or_no_validated_hps)(observedhps, client_states))) {
          struct node* ex = not_forall(retired, (was_observed_or_no_validated_hps)(observedhps, client_states));
          assert ! ((was_observed_or_no_validated_hps)(observedhps, client_states, ex));
          forall_elim(retired, (was_observed_or_no_validated_hps)(observedhps, old_client_states), ex);
          if(!mem(ex, observedhps)) {
            update_hp_preserves_no_validated_hps(ex, action_client, action_n, old_client_states); 
          }
        }
      }
    }
    preserved_by validate_hazard_pointer(action_client) {
      switch(old_nodes) {
        case nil:
        case cons(hh, tt):
      }
      validate_hp_preserves_clients(action_client, old_client_states);
      validate_hp_preserves_hps(client, action_client, old_client_states);
      validate_hp_preserves_length(action_client, old_client_states);
      validate_hp_preserves_handles(client, action_client, old_client_states);
      validate_hp_preserves_is_valid(client, action_client, old_client_states);
      if(!phase2) {
        if(get_hp(action_client, old_client_states) != old_top) {  
        } else {
          if(!forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, client_states)))) {
             struct node* ex = not_forall(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, client_states)));
             forall_elim(retired, (was_observed_or_no_validated_hps)(observedhps, take(index, old_client_states)), ex);
             forall_elim(retired, (is_good_retired)(junk, client), ex);
             if(!mem(ex, observedhps)) {
               take_validate_hp(action_client, old_client_states, index);
               assert no_validated_hps(ex, take(index, old_client_states)) == true;
               if(ex != old_top) {
                 if(mem(action_client, project_stack_clients(take(index, old_client_states)))) {
                   take_mem_project(old_client_states, action_client, index);
                 }
                 validate_different_hp_preserves_no_validated_hps(ex, action_client, take(index, old_client_states));
               } else {
                 forall_elim(nodes, (not_contains)(project_nodes(junk)), ex);
                 mem_project_nodes(old_junk, ex, client);
               }
             }
           }
        }
      } else {
        if(get_hp(action_client, old_client_states) != old_top) {
        } else {
          if(!forall(retired, (was_observed_or_no_validated_hps)(observedhps, client_states))) {
            struct node* ex = not_forall(retired, (was_observed_or_no_validated_hps)(observedhps, client_states));
            assert ! ((was_observed_or_no_validated_hps)(observedhps, client_states, ex));
            forall_elim(retired, (was_observed_or_no_validated_hps)(observedhps, old_client_states), ex);
            forall_elim(retired, (is_good_retired)(junk, client), ex);
            if(!mem(ex, observedhps)) {
              assert no_validated_hps(ex, old_client_states) == true;
              if(ex != old_top) {
                validate_different_hp_preserves_no_validated_hps(ex, action_client, old_client_states); 
              } else {
                forall_elim(nodes, (not_contains)(project_nodes(junk)), ex);
                mem_project_nodes(old_junk, ex, client);
              }
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
  }
  
  handle_predicate phase2_handle(struct stack_client* client, list<struct node*> retired, list<struct node*> todos, list<struct node*> observedhps) {
    invariant mem(client,  project_stack_clients(client_states)) == true &&
              forall(todos, (is_good_retired)(junk, client)) && 
              forall(retired, (is_good_retired)(junk, client)) && 
              get_handle(client, client_states) == predicateHandle &&
              forall(todos, (was_observed_or_no_validated_hps)(observedhps, client_states));
              
    preserved_by noop() { }
    preserved_by push(new_node, v) { }
    preserved_by pop(action_client) {
      if(! forall(todos, (is_good_retired)(junk, client))) {
        struct node* n = not_forall(todos, (is_good_retired)(junk, client));
        forall_elim(todos, (is_good_retired)(old_junk, client), n);
      }
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
      update_hp_preserves_is_valid(client, action_client, action_n, old_client_states);
      if(!forall(todos, (was_observed_or_no_validated_hps)(observedhps, client_states))) {
        struct node* ex = not_forall(todos, (was_observed_or_no_validated_hps)(observedhps, client_states));
        forall_elim(todos, (was_observed_or_no_validated_hps)(observedhps, old_client_states), ex);
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
      validate_hp_preserves_clients(action_client, old_client_states);
      validate_hp_preserves_hps(client, action_client, old_client_states);
      validate_hp_preserves_length(action_client, old_client_states);
      validate_hp_preserves_handles(client, action_client, old_client_states);
      validate_hp_preserves_is_valid(client, action_client, old_client_states);
      if(get_hp(action_client, old_client_states) != old_top) {
      } else {
        if(!forall(todos, (was_observed_or_no_validated_hps)(observedhps, client_states))) {
          struct node* ex = not_forall(todos, (was_observed_or_no_validated_hps)(observedhps, client_states));
          forall_elim(todos, (was_observed_or_no_validated_hps)(observedhps, old_client_states), ex);
          forall_elim(todos, (is_good_retired)(junk, client), ex);
          if(!mem(ex, observedhps)) {
            if(ex != old_top) {
              validate_different_hp_preserves_no_validated_hps(ex, action_client, old_client_states); 
            } else {
              forall_elim(nodes, (not_contains)(project_nodes(junk)), ex);
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
  }
}
@*/

/*@
predicate one_third_data(struct node* n) =
  [1/3]n->data |-> _;

predicate two_thirds_data(struct node* n) =
  [2/3]n->data |-> _;
  
predicate stack_client(struct stack* s, real f, predicate(list<void*>) I, struct stack_client* client) =
  [f]stack_box(?id, s, I) &*& client != 0 &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& 
  list(rlist, ?retired) &*& client->rcount |-> length(retired) &*& basic_client_handle(ha, id, client, retired) &*&
  foreach(retired, two_thirds_data) &*& distinct(retired) == true;
@*/

/*@
predicate_family stack_push_pre(void* index)();
predicate_family stack_push_post(void* index)();

typedef lemma void stack_push_lemma(predicate(list<void*> vs) I, void* data)();
  requires stack_push_pre(this)() &*& I(?vs);
  ensures stack_push_post(this)() &*& I(cons(data, vs));
@*/

/*@
predicate stack(struct stack* s, predicate(list<void*>) I) =
  stack_box(?id, s, I) &*& malloc_block_stack(s);
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
      assert lseg(?hd, ?lst, ?nds, _);
      assert foreach(?junk, _);
      lseg_mem(hd, lst, new_node);
      junk_mem(junk, new_node);
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

/*@
predicate_family stack_pop_pre(void* index)();
predicate_family stack_pop_post(void* index)(bool success, void* res);

typedef lemma void stack_pop_lemma(predicate(list<void*> vs) I)();
  requires stack_pop_pre(this)() &*& I(?vs);
  ensures stack_pop_post(this)(vs != nil, ?out) &*& (vs == nil ? I(nil) : I(tail(vs)) &*& out == head(vs));
@*/

/*@
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
@*/

void phase1(struct stack* s, struct stack_client* client, struct list* plist)
  //@ requires [?f]stack_box(?id, s, ?I) &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& list(rlist, ?retired) &*& client->rcount |-> length(retired) &*& list(plist, nil) &*& basic_client_handle(ha, id, client, retired);
  //@ ensures [f]stack_box(id, s, I) &*& client->rlist |-> rlist &*& [1/2]client->myhandle |-> ha &*& list(rlist, retired) &*& client->rcount |-> length(retired) &*& list(plist, ?hazards) &*& phase2_handle(ha, id, client, nil, retired, hazards);
{
  ;
  /*@
  consuming_box_predicate stack_box(id, s, I)
  consuming_handle_predicate basic_client_handle(ha, client, retired)
  perform_action noop() atomic
  { 
    open myclients(_, _);
    open clients(_, _, ?client_states);
    @*/ struct stack_client* curr = atomic_load_pointer(&s->clients); /*@
    if(! forall(retired, (was_observed_or_no_validated_hps)(nil, take(0, client_states)))) {
      not_forall(retired, (was_observed_or_no_validated_hps)(nil, take(0, client_states)));
    }
  }
  producing_handle_predicate phase1_handle(client, retired, curr, 0, true, nil, false);
  @*/
  //@ int i = 0;
  while(curr != 0) 
    /*@ invariant [f]stack_box(id, s, I) &*& 0 <= i &*& list(plist, ?hps) &*& phase1_handle(ha, id, client, retired, curr, i, true, hps, curr == 0);
    @*/
  {
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate phase1_handle(ha, client, retired, curr, i, true, hps, false)
    perform_action noop() atomic
    {
      open myclients(_, _);
      assert clients(?head, 0,  ?states);
      assert foreach(?junk, _);
      assert i < length(states);
      clients_split(head, curr);
      assert clients(head, curr, ?thestates1);
      assert clients(curr, 0, ?thestates2);
      @*/ struct node* hp = atomic_load_pointer(&curr->hp); /*@
      list<struct node*> nhps = hp == 0 ? hps : cons(hp, hps);
      assert clients(curr, 0, cons(client_state(curr, hp, ?valid, ?curract, ?currha), ?rest));
      struct stack_client* currnext = curr->next;
      open clients(currnext, 0, _);
      clients_merge(head, curr);
      clients_distinct(head, 0);
      nth_append2(thestates1, thestates2, 0);
      assert(length(thestates1) == index_of(curr, project_stack_clients(states)));
      
      nth_index_of(i, project_stack_clients(states));
      assert length(thestates1) == i;
      assert client_state(curr, hp, valid, curract, currha) == nth(i, states);
      if(! forall(retired, (was_observed_or_no_validated_hps)(hp == 0 ? hps : cons(hp, hps), take(i + 1, states)))) {
        struct node* ex = not_forall(retired, (was_observed_or_no_validated_hps)(hp == 0 ? hps : cons(hp, hps), take(i + 1, states)));
        forall_elim(retired, (was_observed_or_no_validated_hps)(hps, take(i, states)), ex);
        assert ! was_observed_or_no_validated_hps(hp == 0 ? hps : cons(hp, hps), take(i + 1, states), ex);
        assert ! (mem(ex, nhps) || no_validated_hps(ex, take(i + 1, states)));
        if(mem(ex, nhps)) {
        } else {
          forall_elim(retired, (is_good_retired)(junk, client), ex);
          append_no_validated_hps(ex, take(i, states), cons(nth(i, states), nil));
          take_plus_one(i, states);
        }
      }
    }
    producing_handle_predicate phase1_handle(client, retired, curr, i + 1, false, hp == 0 ? hps : cons(hp, hps), false);
    @*/
    if(hp != 0) {
      list_add_first(plist, hp);
    }
    
    /*@
    consuming_box_predicate stack_box(id, s, I)
    consuming_handle_predicate phase1_handle(ha, client, retired, curr, i + 1, false, hp == 0 ? hps : cons(hp, hps), false)
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
      clients_distinct(head_, 0);
      nth_index_of(i, project_stack_clients(states_));
      append_project_stack_clients(states1, states2);
      assert i + 1 <= length(states_);
      if(curr != 0) {
        nth_append2( project_stack_clients(states1),  project_stack_clients(states2), 1);
      }
    }
    producing_handle_predicate phase1_handle(client, retired, curr, i + 1, true, hp == 0 ? hps : cons(hp, hps), curr == 0);
    @*/
    //@ i++;
  }
  /*@ if(curr == 0) {
      consuming_box_predicate stack_box(id, s, I)
      consuming_handle_predicate phase1_handle(ha, client, retired, curr, i, true, hps, true)
      perform_action noop() atomic
      {
      }
      producing_handle_predicate phase2_handle(client, nil, retired, hps);
    } @*/
}

/*@
fixpoint bool not_contains<t>(list<t> xs, t x) {
  return ! mem(x, xs); 
}

lemma void not_contains_remove_project_nodes(list<pair<struct node*, struct stack_client*> > junk, struct node* n, struct stack_client* c, struct node* nn)
  requires ! mem(nn, project_nodes(junk));
  ensures ! mem(nn, project_nodes(remove(pair(n, c), junk)));
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
  //@ requires [?f]stack_box(?id, s, ?I) &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& list(rlist, ?retired) &*& distinct(retired) == true &*& client->rcount |-> length(retired) &*& list(plist, ?hazards) &*& phase2_handle(ha, id, client, nil, retired, hazards) &*& foreach(retired, two_thirds_data);
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
                  list(tmplist, ?todos) &*& list(plist, hazards) &*& [1/2]client->myhandle |-> ha &*& phase2_handle(ha, id, client, newretired, todos, hazards) &*&
                  foreach(newretired, two_thirds_data) &*& foreach(todos, two_thirds_data) &*& distinct(newretired) == true &*& distinct(todos) == true &*&
                  forall(todos, (not_contains)(newretired)) == true;
                   @*/
  {
    struct node* curr = list_remove_first(tmplist);
    if(list_contains(plist, curr)) {
      list_add_first(client->rlist, curr);
      client->rcount++;
      //@ open foreach(todos, two_thirds_data);
      //@ close foreach(cons(head(todos), newretired), two_thirds_data);
      /*@
      consuming_box_predicate stack_box(id, s, I)
      consuming_handle_predicate phase2_handle(ha, client, newretired, todos, hazards)
      perform_action noop() atomic
      {
        
      }
      producing_handle_predicate phase2_handle(client, cons(curr, newretired), tail(todos), hazards);
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
      consuming_handle_predicate phase2_handle(ha, client, newretired, todos, hazards)
      perform_action release_node(client, curr) atomic
      {
        open myclients(_, _);
        assert clients(_, _, ?client_states);
        assert foreach(?junk, _);
        assert lseg(_, _, ?nodes, _);
        switch(todos) { case nil: case cons(currr, rest): }
        forall_elim(todos, (was_observed_or_no_validated_hps)(hazards, client_states), curr);
        foreach_remove(pair(curr, client), junk);
        if(! forall(newretired, (is_good_retired)(remove(pair(curr, client), junk), client))) {
          struct node* ex = not_forall(newretired, (is_good_retired)(remove(pair(curr, client), junk), client));
          forall_elim(newretired, (is_good_retired)(junk, client), ex);
          neq_mem_remove(pair(ex, client), pair(curr, client), junk);
        }
        
        if(! forall(tail(todos), (is_good_retired)(remove(pair(curr, client), junk), client))) {
           struct node* ex = not_forall(tail(todos), (is_good_retired)(remove(pair(curr, client), junk), client));
           forall_elim(todos, (is_good_retired)(junk, client), ex);
           neq_mem_remove(pair(ex, client), pair(curr, client), junk);
        }
        if(! forall(nodes, (not_contains)(project_nodes(remove(pair(curr, client), junk))))) {
           struct node* ex = not_forall(nodes, (not_contains)(project_nodes(remove(pair(curr, client), junk))));
           forall_elim(nodes, (not_contains)(project_nodes(junk)), ex);
           not_contains_remove_project_nodes(junk, curr, client, ex);
        }
        junk_mem_remove(junk, curr, client);
        distinct_remove(curr, project_nodes(junk));
      }
      producing_handle_predicate phase2_handle(client, newretired, tail(todos), hazards);
      @*/
      //@ foreach_remove(curr, todos);
      //@ open two_thirds_data(curr);
      //@ open is_node(pair(curr, client));
      free(curr);
    }
   
  }
  list_dispose(tmplist);
  /*@
  consuming_box_predicate stack_box(id, s, I)
  consuming_handle_predicate phase2_handle(ha, client, newretired, nil, hazards)
  perform_action noop() atomic
  {
    
  }
  producing_handle_predicate basic_client_handle(client, newretired);
  @*/
  //@ open foreach(todos, two_thirds_data);
}


void retire_node(struct stack* s, struct stack_client* client, struct node* n)
  //@ requires [?f]stack_box(?id, s, ?I) &*& client->rlist |-> ?rlist &*& [1/2]client->myhandle |-> ?ha &*& list(rlist, ?retired) &*& client->rcount |-> length(retired) &*& distinct(retired) == true &*& is_junk(ha, id, client, retired, true, n) &*& n != 0 &*& [2/3]n->data |-> ?data &*& foreach(retired, two_thirds_data);
  //@ ensures [f]stack_box(id, s, I) &*& client->rlist |-> rlist &*& [1/2]client->myhandle |-> ha &*& list(rlist, ?retired2) &*& client->rcount |-> length(retired2)  &*& distinct(retired2) == true &*& basic_client_handle(ha, id, client, retired2) &*& foreach(retired2, two_thirds_data);
{
  list_add_first(client->rlist, n);
  //@ foreach_two_thirds_mem(retired, n);
  //@ close two_thirds_data(n);
  //@ close foreach(cons(n, retired), two_thirds_data);
  client->rcount++;
  int R = 10;
    /*@
  consuming_box_predicate stack_box(id, s, I)
  consuming_handle_predicate is_junk(ha, client, retired, true, n)
  perform_action noop() atomic
  { 
  @*/ ; /*@
  }
  producing_handle_predicate basic_client_handle(client, cons(n, retired));
  @*/
  if(client->rcount > R) {
    struct list* plist = create_list();
    phase1(s, client, plist);
    phase2(s, client, plist);
    list_dispose(plist);
  }
}

/*@
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
      } else {
        
      }
  }
  close foreach(retired, two_thirds_data);
}

lemma void append_update_hp(list<client_state> states1, list<client_state> states2, struct stack_client* client, struct node* n)
  requires ! mem(client, project_stack_clients(states1));
  ensures update_hp(client, n, append(states1, states2)) == append(states1, update_hp(client, n, states2));
{
  switch(states1) {
    case nil:
    case cons(h, t):
      switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          append_update_hp(t, states2, client, n); 
      }
  }
}

lemma void append_validate_hp(list<client_state> states1, list<client_state> states2, struct stack_client* client)
  requires ! mem(client, project_stack_clients(states1));
  ensures validate_hp(client, append(states1, states2)) == append(states1, validate_hp(client, states2));
{
  switch(states1) {
    case nil:
    case cons(h, t):
      switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          append_validate_hp(t, states2, client); 
      }
  }
}

lemma void validate_hp_is_valid(list<client_state> states, struct stack_client* client)
  requires mem(client, project_stack_clients(states)) == true;
  ensures is_valid(client, validate_hp(client, states)) == true;
{
  switch(states) {
    case nil:
    case cons(h, t):
      switch(h) {
        case client_state(client0, hp0, valid0, active0, ha0):
          if(client0 != client) {
            validate_hp_is_valid(t, client); 
          }
      }
  }
}
@*/

/*@
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
  requires foreach(junk, is_node) &*& mem(n, project_nodes(junk)) == true;
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
  requires foreach(remove_node(junk, n), is_node) &*& mem(n, project_nodes(junk)) == true &*& is_node(pair(n, ?owner)) &*& get_owner(n, junk) == owner;
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
@*/

bool stack_pop(struct stack* s, struct stack_client* client, void** out)
  //@ requires stack_client(s, ?f, ?I, client) &*& pointer(out, ?initial) &*& is_stack_pop_lemma(?lem, I) &*& stack_pop_pre(lem)();
  //@ ensures stack_client(s, f, I, client) &*& pointer(out, ?res) &*& stack_pop_post(lem)(result, ?pst) &*& result ? pst == res : true;
{
  struct node* t, n, tmp, old;
  void* data;
  while(true)
    //@ invariant stack_client(s, f, I, client) &*& pointer(out, initial) &*& is_stack_pop_lemma(lem, I) &*& stack_pop_pre(lem)();
  {
    //@ open stack_client(s, f, I, client);
    /*@
    consuming_box_predicate stack_box(?id, s, I)
    consuming_handle_predicate basic_client_handle(?ha, client, ?retired)
    perform_action noop() atomic
    {
      @*/ t = atomic_load_pointer(&s->top); /*@
      if(t == 0) {
        open lseg(_, _, _, _);
        lem();
      }
    } 
    producing_handle_predicate basic_client_handle(client, retired);
    @*/
    if(t == 0) {
      //@ close stack_client(s, f, I, client);
      //@ leak is_stack_pop_lemma(lem, I);
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
      append_update_hp(states1, states2, client, t);
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
      @*/ tmp = atomic_load_pointer(&s->top); /*@
      if(tmp == t) {
        open myclients(_, ?states_);
        assert clients(?head_, 0, states_);
        clients_split(head_, client);
        assert clients(head_, client, ?states1_);
        assert clients(client, 0, ?states2_);
        client->valid = true;
        clients_merge(head_, client);
        assert clients(head_, 0, ?poststates_);
        append_validate_hp(states1_, states2_, client);
        validate_hp_preserves_hps(client, client, states_);
        validate_hp_preserves_handles(client, client, states_);
        validate_hp_preserves_clients(client, states_);
        validate_hp_is_valid(states_, client);
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
        assert lseg(top, 0, ?nodes, ?vs);
        if(mem(t, project_nodes(junk))) {
          junk_remove(junk, t);
          open is_node(_);
        } else {
          lseg_split(top, 0, t);
        }
        @*/ n = atomic_load_pointer(&t->next); /*@
        close node_next(t, _);
        assert n == t->next;
        if(mem(t, project_nodes(junk))) {
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
      producing_handle_predicate was_top_with_next(client, retired, t, n);
      @*/
      /*@
      consuming_box_predicate stack_box(id, s, I)
      consuming_handle_predicate was_top_with_next(ha, client, retired, t, n)
      perform_action pop(client) atomic
      {
        open lseg(_, _, ?thenodes, _);
        open myclients(s, _);
        assert clients(_, _, ?states__);
        assert foreach(?thejunk, _);
        @*/ old = atomic_compare_and_set_pointer(&s->top, t, n); /*@
        close stack_top(s, _);
        if(old == t) {
          assert foreach(?junk_, is_node);
          open lseg(_, _, _, _);
          t->owner = client;
          close is_node(pair(t, client));
          close foreach(cons(pair(t, client), junk_), is_node);
          lem();
          if(! forall(retired, (is_good_retired)(cons(pair(t, client), junk_), client))){
            struct node* ex = not_forall(retired, (is_good_retired)(cons(pair(t, client), junk_), client));
            forall_elim(retired, (is_good_retired)(junk_, client), ex);
          }
          if(!forall(tail(thenodes), (not_contains)(project_nodes(cons(pair(t, client), junk_))))){
            struct node* ex = not_forall(tail(thenodes), (not_contains)(project_nodes(cons(pair(t, client), junk_))));
            forall_elim(thenodes, (not_contains)(project_nodes(junk_)), ex);
          }    
        }
      }
      producing_handle_predicate is_junk(client, retired, old == t, t);
      @*/
      if(old == t) {
        /*@
        consuming_box_predicate stack_box(id, s, I)
        consuming_handle_predicate is_junk(ha, client, retired, true, t)
        perform_action noop() atomic
        {
          assert foreach(?junk__, _);
          foreach_remove(pair(t, client), junk__);
          open is_node(pair(t, client));
          @*/ data = atomic_load_pointer(&t->data); /*@
          close is_node(pair(t, client));
          foreach_unremove(pair(t, client), junk__);
        }
        producing_handle_predicate is_junk(client, retired, true, t);
        @*/
        retire_node(s, client, t);
        //@ close stack_client(s, f, I, client);
        //@ leak is_stack_pop_lemma(lem, I);
        *out = data;
        return true;
      } else {
        /*@
        consuming_box_predicate stack_box(id, s, I)
        consuming_handle_predicate is_junk(ha, client, retired, false, t)
        perform_action noop() atomic
        {
          @*/ ; /*@
        } 
        producing_handle_predicate basic_client_handle(client, retired);
        @*/
        //@ close stack_client(s, f, I, client);
      }
    }
  }
}

