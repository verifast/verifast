#include "../simplelock.h"
#include "concurrentqueue.h"
#include "stdlib.h"

struct node {
  int value;
  struct node* next;
};

struct queue {
  struct node* head;
  struct lock* lock;
};

/*@
predicate lseg(struct node* from, struct node* to; list<int> vs) =
  from == to ?
    vs == nil
  :
    from != 0 &*& from->next |-> ?next &*& from->value |-> ?value &*& lseg(next, to, ?nvs) &*&
    vs == cons(value, nvs) &*& malloc_block_node(from);

predicate_ctor lock_invariant(struct queue* q, predicate(list<int>) I)() = 
  q->head |-> ?head &*& lseg(head, 0, ?vs) &*& malloc_block_queue(q) &*& I(vs);

predicate queue(struct queue* q, predicate(list<int>) I) = 
  q->lock |-> ?lock &*& is_lock(lock, lock_invariant(q, I));
@*/

struct queue* create_queue()
  //@ requires exists<predicate(list<int> xs)>(?I) &*& I(nil);
  //@ ensures result == 0 ? I(nil) : queue(result, I);
{
  //@ open exists(I);
  struct queue* q = malloc(sizeof(struct queue));
  if(q == 0) return 0;
  q->head = 0;
  //@ close lock_invariant(q, I)();
  //@ close exists(lock_invariant(q, I));
  struct lock* l = create_lock();  
  if(l == 0) {
    abort();
    // todo: figure out a way to prove vs == nil 
    return 0;
  }
  q->lock = l;
  //@ close queue(q, I);
  return q;
}

void enqueue(struct queue* q, int x)
  //@ requires [?f]queue(q, ?I) &*& is_queue_enqueue(?lem, I, x) &*& enqueue_pre(lem)();
  //@ ensures [f]queue(q, I) &*& enqueue_post(lem)();
{
  struct node* new_node = malloc(sizeof(struct node));
  if(new_node == 0) abort();
  new_node->next = 0;
  new_node->value = x;
  //@ open [f]queue(q, I);
  lock_acquire(q->lock);
  //@ open lock_invariant(q, I)();
  //@ open lseg(_, _, _);
  struct node* curr = q->head;
  if(curr == 0) {
    q->head = new_node;
  } else {
    while(true) 
      //@ requires curr != 0 &*& lseg(curr, 0, ?cvs) &*& lseg(new_node, 0, cons(x, nil));
      //@ ensures lseg(old_curr, 0, append(cvs, cons(x, nil))); 
    {
      //@ open lseg(curr, 0, cvs);
      if(curr->next == 0) {
      //@ open lseg(0, 0, _);
        curr->next = new_node;
        break;
      } 
      curr = curr->next;
      //@ recursive_call();
    }
  }
  lem();
  //@ leak is_queue_enqueue(_, _, _);
  //@ close lock_invariant(q, I)();
  lock_release(q->lock);
  //@ close [f]queue(q, I);
}


bool try_dequeue(struct queue* q, int* res)
  //@ requires [?f]queue(q, ?I) &*& integer(res, ?v) &*& is_queue_try_dequeue(?lem, I) &*& try_dequeue_pre(lem)();
  //@ ensures [f]queue(q, I) &*& integer(res, ?nv) &*& try_dequeue_post(lem)(result, ?ret) &*& result ? ret == nv : true;
{
  //@ open [f]queue(q, I);
  lock_acquire(q->lock);
  //@ open lock_invariant(q, I)();
  //@ open lseg(q->head, 0, ?vs);
  if(q->head == 0) {
    lem();
    //@ close lock_invariant(q, I)();
    lock_release(q->lock);
    return false;
    //@ leak is_queue_try_dequeue(_, _);
    //@ close [f]queue(q, I);
  } else {
    lem();
    struct node* head = q->head;
    q->head = q->head->next;
    *res = head->value;
    free(head);
    //@ close lock_invariant(q, I)();
    lock_release(q->lock);
    //@ close [f]queue(q, I);
    //@ leak is_queue_try_dequeue(_, _);
    return true;
  }
}
