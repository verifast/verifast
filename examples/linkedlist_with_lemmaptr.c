#include "stdlib.h"

struct node {
  int value;
  struct node* next;
};

struct list {
  struct node* head;
};

/*@
predicate lseg(struct node* from, struct node* to; list<int> vs) =
  from == to ?
    vs == nil
  :
    from != 0 &*& from->value |-> ?value &*& from->next |-> ?next &*& malloc_block_node(from) &*&
    lseg(next, to, ?vs2) &*& vs == cons(value, vs2);

predicate list(struct list* l; list<int> vs) =
  l->head |-> ?head &*& lseg(head, 0, vs) &*& malloc_block_list(l);
  
lemma_auto void lseg_zero()
  requires lseg(?from, ?to, ?vs);
  ensures lseg(from, to, vs) &*& true && (from == to) == (vs == nil);
{
  open lseg(from, to, vs);
}
    
typedef lemma void update_last(predicate() p, struct node* head, struct node* curr, list<int> vs, int x)();
  requires p() &*& curr->next |-> ?new_node &*& lseg(new_node, 0, cons(x, nil));
  ensures lseg(head, 0, append(vs, cons(x, nil)));
@*/

struct list* create_list()
  //@ requires true;
  //@ ensures result != 0 ? list(result, nil) : true;
{
  struct list* l = malloc(sizeof(struct list));
  if(l == 0) return 0;
  l->head = 0;
  return l;
}

void add(struct list* l, int x)
  //@ requires list(l, ?vs);
  //@ ensures list(l, append(vs, cons(x, nil)));
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->next = 0;
  nn->value = x;
  if(l->head == 0) {
    l->head = nn;
    return;
  }
  //@ struct node* head = l->head;
  struct node* curr = l->head;
  //@ open lseg(head, 0, vs);
  for(;;)
    //@ requires curr != 0 &*& lseg(curr, 0, ?cvs);
    //@ ensures is_update_last(_, ?pred, old_curr, curr, cvs, x) &*& pred() &*& curr->next |-> _;
  {
    //@ struct node* currnext = curr->next;
    //@ int currval = curr->value;
    if(curr->next == 0) {
      /*@
      {
        predicate P() = 
          old_curr->value |-> currval &*& malloc_block_node(old_curr);
    
        lemma void update_last_curr()
          requires P() &*& curr->next |-> ?new_node &*& lseg(new_node, 0, cons(x, nil));
          ensures lseg(old_curr, 0, append(cvs, cons(x, nil)));
        {
          open P();
          close lseg(new_node, 0, cons(x, nil));
        } 
        produce_lemma_function_pointer_chunk(update_last_curr) : update_last(P, old_curr, curr, cvs, x)() { call(); };
        close P();
      } @*/
      break;
    }
    
    curr = curr->next;
    //@ recursive_call();
    //@ assert is_update_last(?doit0, ?P0, currnext, curr, tail(cvs), x);
    /*@
    {
      predicate P() = 
        old_curr->next |-> currnext &*& old_curr->value |-> currval &*& 
        malloc_block_node(old_curr) &*& P0() &*&
        is_update_last(doit0, P0, currnext, curr, tail(cvs), x);
    
      lemma void update_last_curr()
        requires P() &*& curr->next |-> ?new_node &*& lseg(new_node, 0, cons(x, nil));
        ensures lseg(old_curr, 0, append(cvs, cons(x, nil)));
      {
        open P();
        doit0();
        leak is_update_last(_, _, _, _, _, _);
      } 
      produce_lemma_function_pointer_chunk(update_last_curr) : update_last(P, old_curr, curr, cvs, x)() { call(); };
      close P();
    } @*/
  }  
  curr->next = nn;
  //@ assert is_update_last(?lem, _, _, _, _, _);
  //@ lem();
  //@ leak is_update_last(_, _, _, _, _, _);
}