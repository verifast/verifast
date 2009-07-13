// Simple contract for higher-order function "map"
// > no precondition
// > pure functions only

#include "stdlib.h"

struct node {
  int value;
  struct node* next;
};

struct list {
  struct node* head;
};

/*@
inductive list = | nil | cons(int, list);

predicate foreach(list l1, list l2, predicate(int a, int b) q) =
  switch(l1) {
    case nil: return l2 == nil;
    case cons(h1, t1): return
      switch(l2) { 
        case nil: return false;
        case cons(h2, t2): return q(h1, h2) &*& foreach(t1, t2, q);
      };
  };

predicate lseg(struct node* from, struct node* to, list v) =
  from == to ? v == nil : from->next |-> ?n &*& from->value |-> ?val &*& malloc_block_node(from) &*& lseg(n, to, ?nval) &*& v == cons(val, nval);

predicate list(struct list* list, list v) =
  list->head |-> ?h &*& lseg(h, 0, v) &*& malloc_block_list(list);
  
fixpoint int ith(list l, int i) {
  switch(l) {
    case nil: return 0;
    case cons(h, t): return i == 0 ? h : ith(t, i - 1);
  }
}

fixpoint int length(list l) {
  switch(l) {
    case nil: return 0;
    case cons(h, t): return 1 + length(t);
  }
}
@*/

struct list* create_list()
  //@ requires true;
  //@ ensures list(result, nil);
{
  struct list* l = malloc(sizeof(struct list));
  if(l == 0) { abort(); }
  l->head = 0;
  //@ close lseg(0, 0, nil);
  //@ close list(l, nil);
  return l;
}

void addFirst(struct list* l, int x)
  //@ requires list(l, ?v);
  //@ ensures list(l, cons(x, v));
{
  //@ open list(l, v);
  
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) { abort(); }
  n->value = x;
  n->next = l->head;
  l->head = n;
  //@ close lseg(n, 0, cons(x, v));
  //@ close list(l, cons(x, v));
}

int list_ith(struct list* l, int i)
  //@ requires list(l, ?v) &*& 0 <= i &*& i < length(v);
  //@ ensures list(l, v) &*& result == ith(v, i);
{
  //@ open list(l, v);
  int tmp = nodes_ith(l->head, i);
  //@ close list(l, v);
  return tmp;
}

int nodes_ith(struct node* n, int i)
  //@ requires lseg(n, 0, ?v) &*& 0 <= i &*& i < length(v);
  //@ ensures lseg(n, 0, v) &*& result == ith(v, i);
{
  //@ open lseg(n, 0, v);
  if(i == 0) {
    int tmp = n->value;
    //@ close lseg(n, 0, v);
    return tmp;
  } else {
    int tmp = nodes_ith(n->next, i - 1);
    //@ close lseg(n, 0, v);
    return tmp;
  }
}

void dispose_list(struct list* l)
  //@ requires list(l, _);
  //@ ensures true;
{
  //@ open list(l, _);
  struct node* current = l->head;
  while(current != 0) 
    //@ invariant lseg(current, 0, _);
  {
    //@ open lseg(current, 0, _);
    struct node* oldCurrent = current;
    current = current->next;
    free(oldCurrent);
  }
  //@ open lseg(0, 0, _);
  free(l);
}

/*@
predicate_family fmap_pre(void* func)(int x);

predicate_family fmap_post(void* func)(int x, int out);

predicate_family_instance fmap_post(plusOne)(int x, int out) =
  out == x + 1;
  
predicate_ctor fmap_post_ctor(fmap* f)(int a, int b) = 
  fmap_post(f)(a, b);
@*/

typedef int fmap(int x);
  //@ requires true;
  //@ ensures fmap_post(this)(x, result);
  
int plusOne(int x) //@ : fmap
  //@ requires true;
  //@ ensures fmap_post(plusOne)(x, result);
{
  int tmp = x + 1;
  //@ close fmap_post(plusOne)(x, tmp);
  return tmp;
}

void map(struct list* l, void* f)
  //@ requires list(l, ?v) &*& is_fmap(f) == true;
  //@ ensures list(l, ?w) &*& foreach(v, w, fmap_post_ctor(f));
{
  //@ open list(l, v);
  struct node* head = l->head;
  maprec(l->head, f);
  //@ assert lseg(head, 0, ?w);
  //@ close list(l, w);
}

void maprec(struct node* n, fmap* f)
  //@ requires lseg(n, 0, ?v) &*& is_fmap(f) == true;
  //@ ensures lseg(n, 0, ?w) &*& foreach(v, w, fmap_post_ctor(f));
{
  //@ open lseg(n, 0, v);
  if(n == 0) {
    //@ close lseg(n, 0, nil);
    //@ close foreach(nil, nil, fmap_post_ctor(f));
  } else {
    int oldVal = n->value;
    int newVal = f(n->value);
    n->value = newVal;
    struct node* next = n->next;
    maprec(n->next, f);
    //@ assert lseg(next, 0, ?ww);
    //@ close lseg(n, 0, cons(newVal, ww));
    //@ close fmap_post_ctor(f)(oldVal, newVal);
    //@ close foreach(v, cons(newVal, ww), fmap_post_ctor(f));
  }
}

int main() 
  //@ requires true;
  //@ ensures true;
{
  struct list* l = create_list();
  addFirst(l, 5);
  addFirst(l, 10);
  map(l, plusOne);
  //@ open foreach(_, _, _);
  //@ open fmap_post_ctor(plusOne)(_, _);
  //@ open foreach(_, _, _);
  //@ open fmap_post_ctor(plusOne)(_, _);
  //@ open foreach(_, _, _);
  //@ open fmap_post(plusOne)(_, _);
  //@ open fmap_post(plusOne)(_, _);
  
  int tmp = list_ith(l, 0);
  assert tmp == 11;
  int tmp2 = list_ith(l, 1);
  assert tmp2 == 6;
  
  dispose_list(l);
  return 0;
  
}