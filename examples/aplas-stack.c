#include "stdlib.h"

struct node {
  struct node* next;
  int value;
};

struct stack {
  struct node* head;
};

/*@
predicate lseg(struct node* f, struct node* t; list<int> vs) =
  f == t ? vs == nil : f != 0 &*& f->value |-> ?v &*& f->next |-> ?n &*& 
  malloc_block_node(f) &*& lseg(n, t, ?vs0) &*& vs == cons(v, vs0);

predicate stack(struct stack* s; list<int> vs) =
  s->head |-> ?h &*& lseg(h, 0, vs) &*& malloc_block_stack(s);
  
lemma_auto void lseg_inv()
  requires lseg(?f, ?t, ?vs);
  ensures lseg(f, t, vs) &*& true && (f == t ? vs == nil : f != 0 && vs != nil);
{
  open lseg(f, t, vs);
}
@*/

struct stack* create_stack() 
  //@ requires true;
  //@ ensures stack(result, nil);
{
  struct stack* s = malloc(sizeof(struct stack));
  if(s == 0) abort();
  s->head = 0;
  return s;
}

void push(struct stack* s, int x)
  //@ requires stack(s, ?vs);
  //@ ensures stack(s, cons(x, vs));
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = s->head;
  n->value = x;
  s->head = n;
}

int pop(struct stack* s)
  //@ requires stack(s, ?vs) &*& vs != nil;
  //@ ensures stack(s, tail(vs)) &*& result == head(vs);
{
  struct node* tmp = s->head;
  int res = tmp->value;
  s->head = tmp->next;
  free(tmp);
  return res;
}

void dispose(struct stack* s) 
  //@ requires stack(s, ?vs);
  //@ ensures true;
{
  struct node* n = s->head;
  while(n != 0) 
    //@ invariant lseg(n, 0, ?vs0);
    //@ decreases length(vs0);
  {
    struct node* tmp = n;
    n = n->next;
    free(tmp);
  }
  free(s);
}

/*@
lemma void lseg_add(struct node* a)
  requires lseg(a, ?b, ?vs1) &*& b != 0 &*& b->next |-> ?n &*& b->value |-> ?v &*& malloc_block_node(b) &*& lseg(n, 0, ?vs2);
  ensures lseg(a, n, append(vs1, cons(v, nil))) &*& lseg(n, 0, vs2);
{
  if(a == b) {
  } else {
    lseg_add(a->next);
  }
  open lseg(n, 0, vs2);
}

lemma void append_assoc<t>(list<t> l1, list<t> l2, list<t> l3)
  requires true;
  ensures append(l1, append(l2, l3)) == append(append(l1, l2), l3);
{
  switch(l1) {
    case nil: 
    case cons(h, t):
      append_assoc(t, l2, l3);
  }
}
@*/

int get_length(struct stack* s) 
  //@ requires stack(s, ?vs);
  //@ ensures stack(s, vs) &*& result == length(vs);
{
  int r = 0;
  //@ struct node* head = s->head;
  struct node* n = s->head;
  while(n != 0) 
    //@ invariant lseg(head, n, ?vs0) &*& lseg(n, 0, ?vs1) &*& r == length(vs0) &*& vs == append(vs0, vs1);
    //@ decreases length(vs1);
  {
    r = r + 1;
    n = n->next;
    //@ lseg_add(head);
    //@ append_assoc(vs0, cons(head(vs1), nil), tail(vs1));
  }
  return r;
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct stack* s = create_stack();
  push(s, 1);
  push(s, 2);
  push(s, 3);
  int r1 = pop(s);
  int r2 = pop(s);
  int r3 = pop(s);
  //@ assert r3 == 1;
  dispose(s);
  return 0;
}