#include "stdlib.h"

struct node {
  struct node* next;
  int value;
};

struct list {
  struct node* head;
};


struct list* create_list()
  //@ requires true;
  //@ ensures true;
{
  struct list* l = malloc(sizeof(struct list));
  if(l == 0) { abort(); }
  l->head = 0;
  return l;
}

void add(struct list* l, int x)
  //@ requires true;
  //@ ensures true;
{
  struct node* h = add_helper(l->head, x);
  l->head = h;
}

struct node* add_helper(struct node* n, int x)
  //@ requires true;
  //@ ensures true;
{
  struct node* newNode = 0;
  if(n == 0) {
    newNode = malloc(sizeof(struct node));
    if(newNode == 0) { abort(); }
    newNode->value = x;
    newNode->next = 0;
  } else {
    struct node* tmp = add_helper(n->next, x);
    n->next = tmp;
    newNode = n;
  }
  return newNode;
}

int list_length(struct list* l) 
  //@ requires true;
  //@ ensures true;
{
  int myLength = list_length_helper(l->head);
  return myLength;
}

int list_length_helper(struct node* n) 
  //@ requires true;
  //@ ensures true;
{
  if(n == 0) {
    return 0;
  } else {
    int tmp = list_length_helper(n->next);
    return tmp + 1;
  }
}

void dispose(struct list* l) 
  //@ requires true;
  //@ ensures true;
{
  struct node* current = l->head;
  while(current != 0) 
    //@ invariant true;
  {
    struct node* oldcurrent = current;
    current = current->next;
    free(oldcurrent);
  }
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
  
  assert(tmp == 4);
  
  dispose(l);
  return 0;
}


int main2(struct list* l)
  //@ requires true;
  //@ ensures true;
{
  int tmp = list_length(l);
  
  assert(0 <= tmp);
  
  dispose(l);
  return 0;
}




  