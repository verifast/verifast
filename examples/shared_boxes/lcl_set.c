#include "stdlib.h"

//@ #include "ghost_lists.gh"
#include "gotsmanlock.h"

struct lock;

struct node {
  int value;
  struct node* next;
  int lock;
};

struct set {
  struct node* head;
};

/*@
predicate_ctor H(struct node* head)() = 
  head != 0 &*& [1/2]head->value |-> -1000 &*& head->next |-> ?next &*& next != 0 &*&
  lock(&next->lock, N(next)) &*& [1/2]next->value |-> ?nvalue &*& -1000 < nvalue &*&
  malloc_block_node(head);
  
predicate_ctor N(struct node* n)() = 
  n != 0 &*& [1/2]n->value |-> ?value &*& -1000 < value &*& n->next |-> ?next &*&
  (next == 0 ? value == 1000 : lock(&next->lock, N(next)) &*& [1/2]next->value |-> ?nvalue &*& value < nvalue &*& value < 1000) &*&
  malloc_block_node(n);

predicate set(struct set* set, predicate(list<int>) I) =
  set->head |-> ?head &*& head != 0 &*& [1/2]head->value |-> -1000 &*& lock(&head->lock, H(head)) &*& malloc_block_set(set);
@*/

struct set* create_set()
  //@ requires exists<predicate(list<int>)>(?I) &*& I(nil);
  //@ ensures result == 0 ? I(nil) : set(result, I);
{
  struct node* last = malloc(sizeof(struct node));
  if(last == 0) return 0;
  struct node* first = malloc(sizeof(struct node));
  if(first == 0) {
    free(last);
    return 0;
  }
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) {
    free(first);
    free(last);
    return 0;
  }
  first->next = last;
  last->value = 1000;
  last->next = 0;
  first->value = -1000;
  set->head = first;
  //@ close N(last)();
  //@ close exists(N(last));
  init(&last->lock);
  release(&last->lock);
  //@ close H(first)();
  //@ close exists(H(first));
  init(&first->lock);
  release(&first->lock);
  return set;
  //@ close set(set, I);
  //@ leak I(nil); // todo: put in shared box
  //@ open exists(I);
}

void locate(struct node* head, int x, struct node** prev_result, struct node** curr_result)
  //@ requires -1000 < x &*& x < 1000 &*& head != 0 &*& [?f]lock(&head->lock, H(head)) &*& *prev_result |-> _ &*& *curr_result |-> _ &*& [1/2*f]head->value |-> -1000;
  /*@ ensures *prev_result |-> ?prev &*& *curr_result |-> ?curr &*&
              [f]lock(&head->lock, H(head)) &*& lock(&curr->lock, N(curr)) &*& 
              locked(&curr->lock, N(curr)) &*&
              prev != 0 &*& curr != 0 &*& curr != head &*& 
              [1/2]prev->value |-> ?pvalue &*& pvalue < 1000 &*& prev->next |-> curr &*& curr->value |-> ?cvalue &*& pvalue < cvalue &*& -1000 < cvalue &*& 
              curr->next |-> ?cnext &*& cnext != head &*& pvalue < x &*& x <= cvalue &*&
              (cnext == 0 ? cvalue == 1000 : lock(&cnext->lock, N(cnext)) &*& [1/2]cnext->value |-> ?nvalue &*& cvalue < nvalue &*& cvalue < 1000) &*&
              (prev == head ? locked(&head->lock, H(head)) &*& pvalue == -1000 : locked(&prev->lock, N(prev)) &*& -1000 < pvalue) &*&
              malloc_block_node(prev) &*& malloc_block_node(curr) &*& [1/2*f]head->value |-> -1000;
  @*/
{
  struct node* prev = head;
  struct node* curr;
  
  acquire(&head->lock);
  //@ open H(head)();
  curr = prev->next;
  acquire(&curr->lock);
  //@ open N(curr)();
  
  //@ if(curr->next == head) { merge_fractions node_value(head, _); }
  while(curr->value < x)
    /*@ invariant [f]lock(&head->lock, H(head)) &*& lock(&curr->lock, N(curr)) &*& 
                  locked(&curr->lock, N(curr)) &*&
                  prev != 0 &*& curr != 0 &*& curr != head &*& 
                  [1/2]prev->value |-> ?pvalue &*& pvalue < 1000 &*& prev->next |-> curr &*& curr->value |-> ?cvalue &*& pvalue < cvalue &*& -1000 < cvalue &*& 
                  curr->next |-> ?cnext &*& cnext != head &*& pvalue < x &*&
                  (cnext == 0 ? cvalue == 1000 : lock(&cnext->lock, N(cnext)) &*& [1/2]cnext->value |-> ?nvalue &*& cvalue < nvalue &*& cvalue < 1000) &*&
                  (prev == head ? locked(&head->lock, H(head)) &*& pvalue == -1000 : locked(&prev->lock, N(prev)) &*& -1000 < pvalue) &*&
                  malloc_block_node(prev) &*& malloc_block_node(curr) &*& [1/2*f]head->value |-> -1000;
    @*/
  {
    /*@
    if(prev == head) {
      close H(head)();
    } else {
      close N(prev)();
    }
    @*/
    release(&prev->lock);
    prev = curr;
    curr = curr->next;
    acquire(&curr->lock);
    //@ open N(curr)();
    //@ if(curr->next == head) { merge_fractions node_value(head, _); }
  }
  *prev_result = prev;
  *curr_result = curr;
}

bool add(struct set* s, int x)
  //@ requires [?f]set(s, ?I) &*& -1000 < x &*& x < 1000;
  //@ ensures [f]set(s, I);
{
  //@ open [f]set(s, I);
  struct node* prev;
  struct node* curr;
  bool result;
  locate(s->head, x, &prev, &curr);
  assert x <= curr->value;
  if(curr->value != x) {
    struct node* new_node = malloc(sizeof(struct node));
    if(new_node == 0) abort();
    new_node->value = x;
    new_node->next = curr;
    prev->next = new_node;
    //@ close exists(N(new_node));
    init(&new_node->lock);
    //@ close N(new_node)();
    release(&new_node->lock);
    result = true;
  } else {
    result = false;
  }
  /*@
  if(prev == s->head) {
    close H(s->head)();
  } else {
    close N(prev)();
  } @*/
  release(&prev->lock);
  //@ close N(curr)();
  release(&curr->lock);
  //@ close [f]set(s, I);
  return result;
}

