#include "stdlib.h"
//@ #include "maps.gh"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
  
};

/*@
predicate lseg(struct node* first, struct node* last, list<void*> vs) =
  first == last ?
    vs == nil
  :
    first->val |-> ?val &*& first->next |-> ?next &*& malloc_block_node(first) &*& lseg(next, last, ?tail) &*& vs == cons(val, tail); 

predicate set(struct set* set, int size, fixpoint(void*, bool) elements) =
  set->head |-> ?head &*& malloc_block_set(set) &*& lseg(head, 0, ?vs) &*& size == length(vs) &*& list_as_set(vs) == elements;

@*/

struct set* create_set()
  //@ requires true;
  //@ ensures result == 0 ? true : set(result, 0, (empty_set));
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close lseg(0, 0, nil);
  //@ close set(set, 0, (empty_set));
  return set;
}

void set_add(struct set* set, void* x)
  //@ requires set(set, ?size, ?elems) &*& elems(x) == false;
  //@ ensures set(set, size + 1, fupdate(elems, x, true));
{
  //@ open set(set, size, elems);
  //@ assert lseg(?head, 0, ?vs);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close lseg(n, 0, cons(x, vs));
  //@ close set(set, size + 1, fupdate(elems, x, true));
}

bool set_contains(struct set* set, void* x)
  //@ requires set(set, ?size, ?elems);
  //@ ensures set(set, size, elems) &*& result ? exists<void *>(?elem) &*& elems(elem) == true &*& (uintptr_t)x == (uintptr_t)elem : !elems(x);
{
  //@ open set(set, size, elems);
  struct node* curr = set->head;
  bool found = false;
  //@ open lseg(curr, 0, ?vss);
  //@ close lseg(curr, 0, vss);
  //@ void *elem = 0;
  while(curr != 0 && ! found) 
    //@ requires lseg(curr, 0, ?vs) &*& curr == 0 ? vs == nil : true;
    //@ ensures lseg(old_curr, 0, vs) &*& old_found ? found && elem == old_elem : found ? (uintptr_t)elem == (uintptr_t)x && (list_as_set(vs))(elem) : !(list_as_set(vs))(x);
  {
    //@ open lseg(curr, 0, vs);
    //@ assert lseg(_, 0, ?tail);
    if(curr->val == x) {
      //@ elem = curr->val;
      found = true;
    }
    curr = curr->next;
    //@ open lseg(curr, 0, tail);
    //@ close lseg(curr, 0, tail);
    //@ recursive_call();
    //@ close lseg(old_curr, 0, vs);
  }
  //@ close set(set, size, elems);
  //@ if (found) close exists(elem);
  return found;
}

void set_dispose(struct set* set)
  //@ requires set(set, ?size, ?elems);
  //@ ensures true;
{
  //@ open set(set, size, elems);
  struct node* curr = set->head;
  while(curr != 0) 
    //@ invariant lseg(curr, 0, _);
  {
    //@ open lseg(curr, 0, _);
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  //@ open lseg(curr, 0, _);
  free(set);
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct set* set = create_set();
  if(set == 0) return 0;
  set_add(set, (void*) 1);
  set_add(set, (void*) 2);
  set_add(set, (void*) 3);
  bool cnt = set_contains(set, (void*) 1);
  assert(cnt);
  set_dispose(set);
  return 0;
}