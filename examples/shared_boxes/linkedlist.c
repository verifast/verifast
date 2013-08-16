#include "stdlib.h"

struct node {
  int value;
  struct node* next;
};

struct list {
  struct node* first;
  int modcount;
  //@ box id;
};

struct iterator {
  struct list* list;
  struct node* next;
  int expected_modcount;
};

/*@
box_class lbox(int modcount, list<struct node*> nodes) {
  invariant true;
  
  action noop();
    requires true;
    ensures modcount == old_modcount && nodes == old_nodes;
  
  action add(struct node* n);
    requires true;
    ensures modcount == old_modcount + 1 && nodes == cons(n, old_nodes);
  
  action remove();
    requires nodes != nil;
    ensures modcount == old_modcount + 1 && nodes == tail(old_nodes);
  
  handle_predicate is_iterator(int expected_modcount, struct node* n) {
    invariant expected_modcount <= modcount &*& (n == 0 || expected_modcount != modcount || mem(n, nodes));
    
    preserved_by noop() {
    }
    
    preserved_by add(action_n) {
    }
    
    preserved_by remove() {
    }
  }
}
@*/

/*@
predicate lseg(struct node* from, struct node* to, list<struct node*> nodes, list<int> values) =
  from == to ?
    values == nil &*& nodes == nil
  :
    from != 0 &*& from->value |-> ?value &*& from->next |-> ?next &*& malloc_block_node(from) &*&
    lseg(next, to, ?nnodes, ?nvalues) &*& values == cons(value, nvalues) &*& nodes == cons(from, nnodes);
    
lemma void lseg_split(struct node* from, struct node* split)
  requires [?f]lseg(from, 0, ?nodes, ?values) &*& mem(split, nodes) == true;
  ensures [f]lseg(from, split, ?nodes1, ?values1) &*& [f]lseg(split, 0, ?nodes2, ?values2) &*& append(nodes1, nodes2) == nodes &*& append(values1, values2) == values;
{
  if(from == split) {
    close [f]lseg(from, from, nil, nil);
  } else {
    open [f]lseg(from, 0, nodes, values);
    lseg_split(from->next, split);
    close [f]lseg(from, split, _, _);
  }
}

lemma void lseg_merge(struct node* from, struct node* split)
  requires [?f]lseg(from, split, ?nodes1, ?values1) &*& [f]lseg(split, 0, ?nodes2, ?values2);
  ensures [f]lseg(from, 0, append(nodes1, nodes2), append(values1, values2));
{
  open [f]lseg(from, split, nodes1, values1);
  if(from == split) {
  } else {
    lseg_merge(from->next, split);
    close [f]lseg(from, 0, _, _);
  }
}

predicate list(struct list* l, list<int> values) = 
  l->first |-> ?first &*& l->modcount |-> ?modcount &*& 
  lseg(first, 0, ?nodes, values) &*& malloc_block_list(l) &*&
  [_]l->id |-> ?id &*& lbox(id, modcount, nodes);
@*/

struct list* create_list()
  //@ requires true;
  //@ ensures result == 0 ? true : list(result, nil);
{
  struct list* l = malloc(sizeof(struct list));
  if(l == 0) return 0;
  l->first = 0;
  l->modcount = 0;
  //@ close lseg(0, 0, nil, nil);
  //@ create_box id = lbox(0, nil);
  //@ l->id = id;
  //@ leak list_id(_, _); 
  //@ close list(l, nil);
  return l;
}

void add(struct list* l, int x)
  //@ requires list(l, ?values);
  //@ ensures list(l, cons(x, values));
{
  //@ open list(l, values);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = l->first;
  n->value = x;
  l->modcount++;
  l->first = n;
  //@ assert lseg(_, _, ?nodes, values);
  //@ close lseg(n, 0, cons(n, nodes), cons(x, values));
  /*@
  consuming_box_predicate lbox(?id, ?modcount, nodes)
  perform_action add(n)
  { }
  producing_box_predicate lbox(modcount + 1, cons(n, nodes));
  @*/
  //@ close list(l, cons(x, values));
}

void remove(struct list* l, int x)
  //@ requires list(l, ?values) &*& values != nil;
  //@ ensures list(l, tail(values));
{
  //@ open list(l, values);
  //@ open lseg(l->first, 0, ?nodes, values);
  struct node* first = l->first;
  l->first = l->first->next;
  free(first);
  l->modcount++;
  /*@
  consuming_box_predicate lbox(?id, ?modcount, nodes)
  perform_action remove()
  { 
  }
  producing_box_predicate lbox(modcount + 1, tail(nodes));
  @*/
  //@ close list(l, tail(values));
}

/*@
predicate iterator(struct iterator* iter, struct list* l, bool hasNext) =
  iter->next |-> ?next &*& iter->expected_modcount |-> ?expected_modcount &*& 
  iter->list |-> l &*& malloc_block_iterator(iter) &*& ! hasNext || next != 0 &*&
  [_]l->id |-> ?id &*& is_iterator(?ha, id, expected_modcount, next);
@*/

struct iterator* create_iterator(struct list* l) 
  //@ requires [?f]list(l, ?values);
  //@ ensures [f]list(l, values) &*& result == 0 ? true : iterator(result, l, _);
{
  struct iterator* iter = malloc(sizeof(struct iterator));
  if(iter == 0) return 0;
  //@ open [f]list(l, values);
  iter->expected_modcount = l->modcount;
  iter->next = l->first;
  iter->list = l;
  //@ open [f]lseg(l->first, 0, ?nodes, values);
  //@ close [f]lseg(l->first, 0, nodes, values);
  /*@
  consuming_box_predicate lbox(?id, ?modcount, nodes)
  perform_action noop()
  { }
  producing_fresh_handle_predicate is_iterator(modcount, iter->next);
  @*/
  //@ close iterator(iter, l, false);
  //@ close [f]list(l, values);
  return iter;
}

bool has_next(struct iterator* iter)
  //@ requires iterator(iter, ?l, _);
  //@ ensures iterator(iter, l, result);
{
  //@ open iterator(iter, l, _);
  return iter->next != 0;
  //@ close iterator(iter, l, iter->next != 0);
}

int next(struct iterator* iter)
  //@ requires iterator(iter, ?l, true) &*& [?f]list(l, ?values);
  //@ ensures iterator(iter, l, _) &*& [f]list(l, values);
{
  //@ open iterator(iter, l, true);
  //@ open [f]list(l, values);
  if(iter->expected_modcount != iter->list->modcount) abort();
  //@ assert [f]lbox(?id, ?modcount, ?nodes);
  //@ assert is_iterator(?ha, ?id2, _, _);
  /*@
  consuming_box_predicate lbox(id, modcount, nodes)
  consuming_handle_predicate is_iterator(ha, ?expected_modcount, ?next)
  perform_action noop() {
  assert [f]l->first |-> ?first;
    lseg_split(l->first, iter->next);
    assert [f]lseg(first, _, ?nodes1, _) &*& [f]lseg(_, 0, ?nodes2, _);
    assert next == iter->next;
    open [f]lseg(iter->next, 0, _, _);
    open [f]lseg(iter->next->next, 0, _, _);
    close [f]lseg(iter->next->next, 0, _, _);
    struct node* new_next = iter->next->next;
    mem_append(new_next, nodes1, nodes2);
  }
  producing_handle_predicate is_iterator(ha, expected_modcount, new_next);
  @*/
  int result = iter->next->value;
  iter->next = iter->next->next;
  //@ close [f]lseg(next, 0, _, _);
  return result;
  //@ close iterator(iter, l, false);
  //@ lseg_merge(first, next);
  //@ close [f]list(l, values);
}


