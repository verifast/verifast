#include "stdlib.h"

struct node {
  struct node* next;
  int value;
};

struct list {
  struct node* head;
};

/*@
predicate list(struct list* l, listval v)
  requires l->head |-> ?head &*& lseg(head, 0, v) &*& malloc_block_list(l);

predicate lseg(struct node* from, struct node* to, listval v)
  requires from == to ? v == nil : 
           from->next |-> ?next &*& from->value |-> ?val &*& malloc_block_node(from) &*& lseg(next, to, ?nextv) &*& v == cons(val, nextv);
           
inductive listval = | nil | cons(int, listval);

fixpoint listval addLast(listval v, int x)
{
  switch(v) {
    case nil: return cons(x, nil);
    case cons(h, t): return cons(h, addLast(t, x));
  }
}

fixpoint int listval_length(listval v)
{
  switch(v) {
    case nil: return 0;
    case cons(h, t): return 1 + listval_length(t);
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

void add(struct list* l, int x)
  //@ requires list(l, ?v);
  //@ ensures list(l, addLast(v, x));
{
  //@ open list(l, v);
  struct node* h = add_helper(l->head, x);
  l->head = h;
  //@ close list(l, addLast(v, x));
}

struct node* add_helper(struct node* n, int x)
  //@ requires lseg(n, 0, ?v);
  //@ ensures lseg(result, 0, addLast(v, x));
{
  //@ open lseg(n, 0, v);
  struct node* newNode = 0;
  if(n == 0) {
    newNode = malloc(sizeof(struct node));
    if(newNode == 0) { abort(); }
    newNode->value = x;
    newNode->next = 0;
    //@ close lseg(0, 0, nil);
  } else {
    struct node* tmp = add_helper(n->next, x);
    n->next = tmp;
    newNode = n;
  }
  //@ close lseg(newNode, 0, addLast(v, x));
  return newNode;
}

int list_length(struct list* l) 
  //@ requires list(l, ?v);
  //@ ensures list(l, v) &*& result == listval_length(v);
{
  //@ open list(l, v);
  int myLength = list_length_helper(l->head);
  //@ close list(l, v);
  return myLength;
}

int list_length_helper(struct node* n) 
  //@ requires lseg(n, 0, ?v);
  //@ ensures lseg(n, 0, v) &*& result == listval_length(v);
{
  //@ open lseg(n, 0, v);
  if(n == 0) {
    //@ close lseg(0, 0, nil);
    return 0;
  } else {
    int tmp = list_length_helper(n->next);
    //@ close lseg(n, 0, v);
    return tmp + 1;
  }
}

void dispose(struct list* l) 
  //@ requires list(l, _);
  //@ ensures true;
{
  //@ open list(l, _);
  struct node* current = l->head;
  while(current != 0) 
    //@ invariant lseg(current, 0, _); 
  {
    //@ open lseg(current, 0, _);
    struct node* oldcurrent = current;
    current = current->next;
    free(oldcurrent);
  }
  //@ open lseg(0, 0, _);
  free(l);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct list* l= create_list();
  add(l, 1);
  add(l, 2);
  add(l, 2);
  add(l, 4);
  
  int tmp = list_length(l);
  
  //@ assert tmp == 4;
  
  dispose(l);
  return 0;
}

/*@
lemma void length_positive_lemma(listval v) 
  requires true;
  ensures 0 <= listval_length(v);
{
  switch(v) {
    case nil:
    case cons(h, t): length_positive_lemma(t);
  }
}
@*/

int main2(struct list* l)
  //@ requires list(l, ?v);
  //@ ensures true;
{
  int tmp = list_length(l);
  //@ length_positive_lemma(v);
  
  //@ assert 0 <= tmp;
  
  dispose(l);
  return 0;
}




  