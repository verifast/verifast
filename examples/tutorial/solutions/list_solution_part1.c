#include "stdlib.h"

struct node {
  struct node* next;
  int value;
};

struct list {
  struct node* head;
};

/*@
predicate list(struct list* l)
  requires l->head |-> ?head &*& lseg(head, 0) &*& malloc_block_list(l);

predicate lseg(struct node* from, struct node* to)
  requires from == to ? true : 
           from->next |-> ?next &*& from->value |-> ?val &*& malloc_block_node(from) &*& lseg(next, to);
@*/

struct list* create_list()
  //@ requires true;
  //@ ensures list(result);
{
  struct list* l = malloc(sizeof(struct list));
  if(l == 0) { abort(); }
  l->head = 0;
  //@ close lseg(0, 0);
  //@ close list(l);
  return l;
}

void add(struct list* l, int x)
  //@ requires list(l);
  //@ ensures list(l);
{
  //@ open list(l);
  struct node* h = add_helper(l->head, x);
  l->head = h;
  //@ close list(l);
}

struct node* add_helper(struct node* n, int x)
  //@ requires lseg(n, 0);
  //@ ensures lseg(result, 0);
{
  //@ open lseg(n, 0);
  struct node* newNode = 0;
  if(n == 0) {
    newNode = malloc(sizeof(struct node));
    if(newNode == 0) { abort(); }
    newNode->value = x;
    newNode->next = 0;
    //@ close lseg(0, 0);
  } else {
    struct node* tmp = add_helper(n->next, x);
    n->next = tmp;
    newNode = n;
  }
  //@ close lseg(newNode, 0);
  return newNode;
}

void dispose(struct list* l) 
  //@ requires list(l);
  //@ ensures true;
{
  //@ open list(l);
  struct node* current = l->head;
  while(current != 0) 
    //@ invariant lseg(current, 0); 
  {
    //@ open lseg(current, 0);
    struct node* oldcurrent = current;
    current = current->next;
    free(oldcurrent);
  }
  //@ open lseg(0, 0);
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
  
  dispose(l);
  return 0;
}
  