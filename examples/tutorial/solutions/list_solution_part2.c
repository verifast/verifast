#include "stdlib.h"

struct node {
  struct node* next;
  int value;
};

struct list {
  struct node* head;
};

/*@
predicate list(struct list* l, int length)
  requires l->head |-> ?head &*& lseg(head, 0, length) &*& malloc_block_list(l);

predicate lseg(struct node* from, struct node* to, int length)
  requires from == to ? length == 0 : 
           from->next |-> ?next &*& from->value |-> ?val &*& malloc_block_node(from) &*& lseg(next, to, length - 1);
@*/

struct list* create_list()
  //@ requires true;
  //@ ensures list(result, 0);
{
  struct list* l = malloc(sizeof(struct list));
  if(l == 0) { abort(); }
  l->head = 0;
  //@ close lseg(0, 0, 0);
  //@ close list(l, 0);
  return l;
}

void add(struct list* l, int x)
  //@ requires list(l, ?length);
  //@ ensures list(l, length + 1);
{
  //@ open list(l, length);
  struct node* h = add_helper(l->head, x);
  l->head = h;
  //@ close list(l, length + 1);
}

struct node* add_helper(struct node* n, int x)
  //@ requires lseg(n, 0, ?length);
  //@ ensures lseg(result, 0, length + 1);
{
  //@ open lseg(n, 0, length);
  struct node* newNode = 0;
  if(n == 0) {
    newNode = malloc(sizeof(struct node));
    if(newNode == 0) { abort(); }
    newNode->value = x;
    newNode->next = 0;
    //@ close lseg(0, 0, 0);
  } else {
    struct node* tmp = add_helper(n->next, x);
    n->next = tmp;
    newNode = n;
  }
  //@ close lseg(newNode, 0, length + 1);
  return newNode;
}

int list_length(struct list* l) 
  //@ requires list(l, ?length);
  //@ ensures list(l, length) &*& result == length;
{
  //@ open list(l, length);
  int myLength = list_length_helper(l->head);
  //@ close list(l, length);
  return myLength;
}

int list_length_helper(struct node* n) 
  //@ requires lseg(n, 0, ?length);
  //@ ensures lseg(n, 0, length) &*& result == length;
{
  //@ open lseg(n, 0, length);
  if(n == 0) {
    //@ close lseg(0, 0, 0);
    return 0;
  } else {
    int tmp = list_length_helper(n->next);
    //@ close lseg(n, 0, length);
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
  