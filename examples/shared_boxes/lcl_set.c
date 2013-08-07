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
predicate_ctor H(struct node* head, box id, box gl, predicate(list<int>) I)() = 
  head != 0 &*& [1/2]head->value |-> -1000 &*& head->next |-> ?next &*& next != 0 &*&
  lock(&next->lock, N(next, id, gl, I)) &*& [1/2]next->value |-> ?nvalue &*& -1000 < nvalue &*&
  malloc_block_node(head) &*& [_]setbox(id, gl, I);
  
predicate_ctor N(struct node* n, box id, box gl, predicate(list<int>) I)() = 
  n != 0 &*& [1/2]n->value |-> ?value &*& -1000 < value &*& n->next |-> ?next &*&  [_]setbox(id, gl, I) &*&
  (next == 0 ? value == 1000 : lock(&next->lock, N(next, id, gl, I)) &*& [1/2]next->value |-> ?nvalue &*& value < nvalue &*& value < 1000 &*& ghost_list_member_handle(gl, value)) &*&
  malloc_block_node(n);

predicate set(struct set* set, predicate(list<int>) I) =
  set->head |-> ?head &*& head != 0 &*& [1/2]head->value |-> -1000 &*& [_]setbox(?id, ?gl, I) &*& lock(&head->lock, H(head, id, gl, I)) &*& malloc_block_set(set);

box_class setbox(box gl, predicate(list<int>) I) {
  invariant ghost_list(gl, ?values) &*& I(values);
  
  action act();
    requires true;
    ensures true;
}
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
  //@ box gl = create_ghost_list();
  //@ create_box id = setbox(gl, I);
  //@ leak setbox(_, gl, I);
  //@ close N(last, id, gl, I)();
  //@ close exists(N(last, id, gl, I));
  init(&last->lock);
  release(&last->lock);
  //@ close H(first, id, gl, I)();
  //@ close exists(H(first, id, gl, I));
  init(&first->lock);
  release(&first->lock);
  return set;
  //@ close set(set, I);
  //@ open exists(I);
}

void locate(struct node* head, int x, struct node** prev_result, struct node** curr_result)
  //@ requires exists<box>(?id) &*& exists<box>(?gl) &*& exists<predicate(list<int>)>(?I) &*& -1000 < x &*& x < 1000 &*& head != 0 &*& [?f]lock(&head->lock, H(head, id, gl, I)) &*& *prev_result |-> _ &*& *curr_result |-> _ &*& [1/2*f]head->value |-> -1000;
  /*@ ensures *prev_result |-> ?prev &*& *curr_result |-> ?curr &*&
              [f]lock(&head->lock, H(head, id, gl, I)) &*& lock(&curr->lock, N(curr, id, gl, I)) &*& 
              locked(&curr->lock, N(curr, id, gl, I)) &*&
              prev != 0 &*& curr != 0 &*& curr != head &*& 
              [1/2]prev->value |-> ?pvalue &*& pvalue < 1000 &*& prev->next |-> curr &*& curr->value |-> ?cvalue &*& pvalue < cvalue &*& -1000 < cvalue &*& 
              curr->next |-> ?cnext &*& cnext != head &*& pvalue < x &*& x <= cvalue &*&
              (cnext == 0 ? cvalue == 1000 : ghost_list_member_handle(gl, cvalue) &*& lock(&cnext->lock, N(cnext, id, gl, I)) &*& [1/2]cnext->value |-> ?nvalue &*& cvalue < nvalue &*& cvalue < 1000) &*&
              (prev == head ? locked(&head->lock, H(head, id, gl, I)) &*& pvalue == -1000 : ghost_list_member_handle(gl, pvalue) &*& locked(&prev->lock, N(prev, id, gl, I)) &*& -1000 < pvalue) &*&
              malloc_block_node(prev) &*& malloc_block_node(curr) &*& [1/2*f]head->value |-> -1000 &*& [_]setbox(id, gl, I);
  @*/
{
  struct node* prev = head;
  struct node* curr;
  
  acquire(&head->lock);
  //@ open H(head, id, gl, I)();
  curr = prev->next;
  acquire(&curr->lock);
  //@ open N(curr, id, gl, I)();
  
  //@ if(curr->next == head) { merge_fractions node_value(head, _); }
  while(curr->value < x)
    /*@ invariant [f]lock(&head->lock, H(head, id, gl, I)) &*& lock(&curr->lock, N(curr, id, gl, I)) &*& [_]setbox(id, gl, I) &*&
                  locked(&curr->lock, N(curr, id, gl, I)) &*&
                  prev != 0 &*& curr != 0 &*& curr != head &*& 
                  [1/2]prev->value |-> ?pvalue &*& pvalue < 1000 &*& prev->next |-> curr &*& curr->value |-> ?cvalue &*& pvalue < cvalue &*& -1000 < cvalue &*& 
                  curr->next |-> ?cnext &*& cnext != head &*& pvalue < x &*&
                  (cnext == 0 ? cvalue == 1000 : ghost_list_member_handle(gl, cvalue) &*& lock(&cnext->lock, N(cnext, id, gl, I)) &*& [1/2]cnext->value |-> ?nvalue &*& cvalue < nvalue &*& cvalue < 1000) &*&
                  (prev == head ? locked(&head->lock, H(head, id, gl, I)) &*& pvalue == -1000 : ghost_list_member_handle(gl, pvalue) &*& locked(&prev->lock, N(prev, id, gl, I)) &*& -1000 < pvalue) &*&
                  malloc_block_node(prev) &*& malloc_block_node(curr) &*& [1/2*f]head->value |-> -1000;
    @*/
  {
    /*@
    if(prev == head) {
      close H(head, id, gl, I)();
    } else {
      close N(prev, id, gl, I)();
    }
    @*/
    release(&prev->lock);
    prev = curr;
    curr = curr->next;
    acquire(&curr->lock);
    //@ open N(curr, id, gl, I)();
    //@ if(curr->next == head) { merge_fractions node_value(head, _); }
  }
  *prev_result = prev;
  *curr_result = curr;
}

/*@
predicate_family set_add_pre(void* index)(int x);
predicate_family set_add_post(void* index)(int x, list<int> old_set);

typedef lemma void set_add_lemma(int x, predicate(list<int>) I)();
  requires set_add_pre(this)(x) &*& I(?values);
  ensures set_add_post(this)(x, values) &*& I(cons(x, values));
@*/

bool add(struct set* s, int x)
  //@ requires [?f]set(s, ?I) &*& -1000 < x &*& x < 1000 &*& is_set_add_lemma(?lem, x, I) &*& set_add_pre(lem)(x);
  //@ ensures [f]set(s, I) &*& set_add_post(lem)(x, ?new_values);
{
  //@ open [f]set(s, I);
  //@ assert [_]setbox(?id, ?gl, I);
  struct node* prev;
  struct node* curr;
  bool result;
  //@ close exists(gl);
  //@ close exists(id);
  //@ close exists(I);
  locate(s->head, x, &prev, &curr);
  //@ handle ha = create_handle setbox_handle(id);
  assert x <= curr->value;
  if(curr->value != x) {
    struct node* new_node = malloc(sizeof(struct node));
    if(new_node == 0) abort();
    new_node->value = x;
    new_node->next = curr;
    prev->next = new_node;
    //@ close exists(N(new_node, id, gl, I));
    init(&new_node->lock);
    /*@
    consuming_box_predicate setbox(id, gl, I)
    consuming_handle_predicate setbox_handle(ha)
    perform_action act() atomic
    {
      ghost_list_add(gl, x);
      lem();
    }
    producing_handle_predicate setbox_handle();
    @*/
    //@ close N(new_node, id, gl, I)();
    release(&new_node->lock);
    result = true;
  } else {
    /*@
    consuming_box_predicate setbox(id, gl, I)
    consuming_handle_predicate setbox_handle(ha)
    perform_action act() atomic
    {
      ghost_list_add(gl, x);
      lem();
    }
    producing_handle_predicate setbox_handle();
    @*/
    //@ leak ghost_list_member_handle(gl, x);
    result = false;
  }
  /*@
  if(prev == s->head) {
    close H(s->head, id, gl, I)();
  } else {
    close N(prev, id, gl, I)();
  } @*/
  release(&prev->lock);
  //@ close N(curr, id, gl, I)();
  release(&curr->lock);
  //@ close [f]set(s, I);
  //@ leak is_set_add_lemma(_, _, _);
  //@ leak setbox_handle(_, _);
  return result;
}

/*@
predicate_family set_contains_pre(void* index)(int x);
predicate_family set_contains_post(void* index)(int x, list<int> elements, bool result);

typedef lemma void set_contains_lemma(int x, predicate(list<int>) I)(bool result);
  requires set_contains_pre(this)(x) &*& I(?values);
  ensures set_contains_post(this)(x, values, result) &*& I(values) &*& !result || mem(x, values);
@*/

bool contains(struct set* s, int x)
  //@ requires [?f]set(s, ?I) &*& -1000 < x &*& x < 1000 &*& is_set_contains_lemma(?lem, x, I) &*& set_contains_pre(lem)(x);
  //@ ensures [f]set(s, I) &*& set_contains_post(lem)(x, ?values, result);
{
  //@ open [f]set(s, I);
  //@ assert [_]setbox(?id, ?gl, I);
  struct node* prev;
  struct node* curr;
  bool result;
  //@ close exists(gl);
  //@ close exists(id);
  //@ close exists(I);
  locate(s->head, x, &prev, &curr);
  result = x == curr->value;
  //@ handle ha = create_handle setbox_handle(id);
  /*@
    consuming_box_predicate setbox(id, gl, I)
    consuming_handle_predicate setbox_handle(ha)
    perform_action act() atomic
    {
      if(result) {
      	ghost_list_member_handle_lemma(gl, x);
      }
      lem(result);
    }
    producing_handle_predicate setbox_handle();
    @*/
    /*@
  if(prev == s->head) {
    close H(s->head, id, gl, I)();
  } else {
    close N(prev, id, gl, I)();
  } @*/
  release(&prev->lock);
  //@ close N(curr, id, gl, I)();
  release(&curr->lock);
  //@ close [f]set(s, I);
  //@ leak is_set_contains_lemma(lem, x, _);
  //@ leak setbox_handle(_, _);
  return result;
}


