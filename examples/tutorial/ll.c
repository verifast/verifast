#include "stdlib.h"

/*@
inductive list = | nil | cons(int, list);

fixpoint list append(list l1, list l2) {
  switch(l1) {
    case nil: return l2;
    case cons(h, t): return cons(h, append(t, l2));
  }
}

predicate lseg(struct node* from, struct node* to, list vs) = 
  from == to ? vs == nil : from->next |-> ?n &*& from->value |-> ?h &*& malloc_block_node(from) &*&lseg(n, to, ?t) &*& vs == cons(h, t);
  
predicate list(struct linkedlist* l, list vs) =
  l->head |-> ?head &*& lseg(head, 0, vs) &*& malloc_block_linkedlist(l);
@*/

struct node {
  struct node* next;
  int value;
};

struct linkedlist {
  struct node* head;
};

struct node* create_node(struct node* next, int value)
  //@ requires true;
  //@ ensures result!=0 &*& result->next |-> next &*& result->value |-> value &*& malloc_block_node(result);
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = next;
  n->value = value;
  return n;
}

struct linkedlist* create_list()
  //@ requires true;
  //@ ensures list(result, nil);
{
  struct linkedlist* l = malloc(sizeof(struct linkedlist));
  if(l == 0) abort();
  l->head = 0;
  //@ close lseg(0, 0, nil);
  //@ close list(l, nil);
  return l;
}

// iterative implementation

/*@
lemma void appendlemma(struct node* head, struct node* current)
  requires lseg(head, current, ?vs1) &*& current!=0 &*& current->next |-> ?n &*& current->value |-> ?v &*& malloc_block_node(current) &*& n->value |-> ?v2;
  ensures lseg(head, n, append(vs1, cons(v, nil))) &*& n->value |-> v2;
{
  if(head == current) {
    open lseg(head, current, vs1);
    close lseg(n, n, nil);
    close lseg(head, n, cons(v, nil));
  } else {
    open lseg(head, current, vs1);
    appendlemma(head->next, current);
    close lseg(head, n, append(vs1, cons(v, nil)));
  }
}
  
lemma void appendlemma2(list vs1, int v, list vs2)
  requires true;
  ensures append(vs1, cons(v, vs2)) == append(append(vs1, cons(v, nil)), vs2);
{
  switch(vs1) {
    case nil: return;
    case cons(h, t): appendlemma2(t, v, vs2);
  }
}
  
lemma void appendlemma3(struct node* n1, struct node* n2)
  requires lseg(n1, n2, ?vs1) &*& lseg(n2, 0, ?vs2);
  ensures lseg(n1, 0, append(vs1, vs2));
{
  if(n1 == n2) {
    open lseg(n1, n2, vs1);  
  } else {
    open lseg(n1, n2, vs1);
    open node_next(n1, _);
    pointer_nonzero(n1);
    close node_next(n1, _);
    appendlemma3(n1->next, n2);
    close lseg(n1, 0, append(vs1, vs2));
  }
}
@*/

void add_iterative(struct linkedlist* l, int x)
  //@ requires list(l, ?vs);
  //@ ensures list(l, append(vs, cons(x, nil)));
{
  //@ open list(l, vs);
  if(l->head == 0) {
    struct node* n = create_node(0, x);
    l->head = n;
    //@ open lseg(0, 0, _);
    //@ close lseg(0, 0, _);
    //@ close lseg(n, 0, cons(x, nil));
    //@ close list(l, append(vs, cons(x, nil)));
  } else {
    struct node* head = l->head;
    struct node* current = l->head;
    //@ close lseg(head, head, nil);
    //@ open lseg(head, 0, vs);
    while(current->next != 0) 
      //@ invariant current!= 0 &*& lseg(head, current, ?vs1) &*& current->value |-> ?v &*& current->next |-> ?n &*& malloc_block_node(current) &*& lseg(n, 0, ?vs2) &*& vs == append(vs1, cons(v, vs2));
    {
      //@ open lseg(n, 0, _);
      struct node* oldcurrent = current;
      current = current->next;
      //@ appendlemma(head, oldcurrent);
      //@ appendlemma2(vs1, v, vs2);
    }
    //@ open lseg(0, 0, _);
    struct node* nn = create_node(0, x);
    current->next = nn;
    //@ close lseg(0, 0, nil);
    //@ close lseg(nn, 0, _);
    //@ close lseg(current, 0, _);
    //@ appendlemma3(head, current);
    //@ appendlemma2(vs1, v, cons(x, nil));
    //@ close list(l, append(vs, cons(x, nil)));
  }
}

void add_recursive(struct linkedlist* l, int x)
  //@ requires list(l, ?vs);
  //@ ensures list(l, append(vs, cons(x, nil)));
{
  //@ open list(l, vs);
  if(l->head == 0) {
    struct node* n = create_node(0, x);
    l->head = n;
    //@ open lseg(0, 0, _);
    //@ close lseg(0, 0, _);
    //@ close lseg(n, 0, cons(x, nil));
  } else {
    addHelper(l->head, x);
  }
  //@ close list(l, append(vs, cons(x, nil)));
}

void addHelper(struct node* n, int x)
  //@ requires n!= 0 &*& lseg(n, 0, ?vs);
  //@ ensures lseg(n, 0, append(vs, cons(x, nil)));
{
  //@ open lseg(n, 0, vs);
  if(n->next == 0) {
    //@ open lseg(0, 0, _);
    //@ close lseg(0, 0, _);
    struct node* nn = create_node(0, x);
    n->next = nn;
    //@ close lseg(nn, 0, cons(x, nil));
  } else {
    addHelper(n->next, x);
  }
  //@ close lseg(n, 0, append(vs, cons(x, nil)));
}
