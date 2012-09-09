#include "stdlib.h"
#include "atomics.h"

struct node {
  int value;
  struct node* next;
};

struct queue {
  //@ struct node* initial;
  struct node* head;
  struct node* tail;
};

/*@
lemma_auto(mem(x, append(xs, ys))) void mem_append<t>(list<t> xs, list<t> ys, t x)
  requires true;
  ensures mem(x, append(xs, ys)) == (mem(x, xs) || mem(x, ys));
{
  switch(xs) {
    case nil:
    case cons(h, t): mem_append(t, ys, x);
  }
}

lemma_auto(index_of(x, append(xs, ys))) void index_of_append<t>(list<t> xs, list<t> ys, t x)
  requires mem(x, xs) == true;
  ensures index_of(x, xs) == index_of(x, append(xs, ys));
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(x != h) 
        index_of_append(t, ys, x);
  }
}

lemma_auto(index_of(x, append(xs, ys))) void index_of_append2<t>(list<t> xs, list<t> ys, t x)
  requires mem(x, ys) == true && !mem(x, xs);
  ensures length(xs) + index_of(x, ys) == index_of(x, append(xs, ys));
{
  switch(xs) {
    case nil:
    case cons(h, t):
        index_of_append2(t, ys, x);
  }
}

lemma_auto(nth(i, append(xs, ys))) void nth_append_auto<t>(list<t> xs, list<t> ys, int i)
  requires 0 <= i && i < length(xs);
  ensures nth(i, xs) == nth(i, append(xs, ys));
{
  nth_append(xs, ys, i);
}
@*/

/*@
lemma void lseg_split(struct node* from, struct node* to, struct node* n)
  requires lseg(from, to, ?nodes, ?vs) &*& mem(n, nodes) == true;
  ensures lseg(from, n, ?nodes1, ?vs1) &*& lseg(n, to, ?nodes2, ?vs2) &*& n != to &*& append(nodes1, nodes2) == nodes && append(vs1, vs2) == vs;
{
  open lseg(from, to, nodes, vs);
  if(from == to) {
  } else {
    if(from == n) {
    } else {
      lseg_split(from->next, to, n);
    }
  }
}

lemma void lseg_merge(struct node* a, struct node* b, struct node* c)
  requires lseg(a, b, ?ns1, ?vs1) &*& lseg(b, c, ?ns2, ?vs2) &*& lseg(c, 0, ?ns3, ?vs3);
  ensures lseg(a, c, append(ns1, ns2), append(vs1, vs2)) &*& lseg(c, 0, ns3, vs3);
{
  open lseg(a, b, ns1, vs1);
  open lseg(c, 0, ns3, vs3);
  if(a != b) {
    lseg_merge(a->next, b, c);
  }
}

lemma_auto(nth(index_of(x, xs), xs)) void index_of_nth<t>(list<t> xs, t x)
  requires mem(x, xs) == true;
  ensures nth(index_of(x, xs), xs) == x; 
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(h == x) {
      } else {
        index_of_nth(t, x);
      }
  }
}

lemma void lseg_next_distinct(struct node* from, struct node* to, struct node* n)
  requires lseg(from, to, ?nodes, ?vs) &*& n->next |-> ?nxt;
  ensures lseg(from, to, nodes, vs) &*& n->next |-> nxt &*& ! mem(n, nodes);
{
  open lseg(from, to, nodes, vs);
  if(from == to) {
  } else {
    lseg_next_distinct(from->next, to, n);
  }
}


lemma void lseg_distinct(struct node* from, struct node* to)
  requires lseg(from, to, ?nodes, ?vs);
  ensures lseg(from, to, nodes, vs) &*& distinct(nodes) == true;
{
  open lseg(from, to, nodes, vs);
  if(from == to) {
  } else {
    lseg_distinct(from->next, to);
    lseg_next_distinct(from->next, to, from);
  }
}

lemma void distinct_mem<t>(list<t> xs, list<t> ys, t x)
  requires distinct(append(xs, ys)) == true &*& mem(x, ys) == true;
  ensures ! mem(x, xs) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(h == x) {
      } else {
        distinct_mem(t, ys, x);
      }
  }
}
@*/

/*@
box_class msqueue_box(struct queue* q, predicate(list<int>) P) {
  invariant q->initial |-> ?initial &*& q->head |-> ?head &*& q->tail |-> ?tail &*& lseg(initial, 0, ?nodes, ?vs) &*&
            mem(head, nodes) == true &*& mem(tail, nodes) == true &*& index_of(head, nodes) <= index_of(tail, nodes) &*&
            length(nodes) - 2 <= index_of(tail, nodes);// &*& P(drop(index_of(head, nodes), vs));
            
  action enqueue(struct node* new_node, int x);
    requires true;
    ensures initial == old_initial && head == old_head && tail == old_tail && 
            nodes == append(old_nodes, cons(new_node, nil)) && vs == append(old_vs, cons(x, nil));
  
  action dequeue();
    requires true;
    ensures initial == old_initial  && tail == old_tail && nodes == old_nodes && vs == old_vs &&
            (head == old_head || index_of(head, nodes) == index_of(old_head, old_nodes) + 1);
            
  action move_tail();
    requires true;
    ensures initial == old_initial && head == old_head  && nodes == old_nodes && vs == old_vs &&
            (tail == old_tail || index_of(tail, nodes) == index_of(old_tail, old_nodes) + 1);
  
  action noop();
    requires true;
    ensures initial == old_initial && head == old_head && tail == old_tail && 
            nodes == old_nodes && vs == old_vs;
  
  handle_predicate was_head(struct node* h) {
    invariant mem(h, nodes) == true && index_of(h, nodes) <= index_of(head, nodes); 
    
    preserved_by enqueue(new_node, x) {}
    preserved_by dequeue() {}
    preserved_by move_tail() {}
    preserved_by noop() {}
  }
  
  handle_predicate was_head_with_succ(struct node* h, struct node* n) {
    invariant mem(h, nodes) == true && index_of(h, nodes) <= index_of(head, nodes) &&
              (n != 0 ? 
                index_of(h, nodes) < length(nodes) - 1 && n == nth(index_of(h, nodes) + 1, nodes) && index_of(h, nodes) + 1 == index_of(n, nodes)
              :
                true
              );
              
    preserved_by enqueue(new_node, x) {}
    preserved_by dequeue() {}
    preserved_by move_tail() {}
    preserved_by noop() {}
  }
  
    handle_predicate was_head_with_succ_not_tail(struct node* h, struct node* n) {
    invariant mem(h, nodes) == true && index_of(h, nodes) <= index_of(head, nodes) && index_of(h, nodes) < index_of(tail, nodes) &&
              (n != 0 ? 
                index_of(h, nodes) < length(nodes) - 1 && n == nth(index_of(h, nodes) + 1, nodes) && index_of(h, nodes) + 1 == index_of(n, nodes)
              :
                true
              );
              
    preserved_by enqueue(new_node, x) {}
    preserved_by dequeue() {}
    preserved_by move_tail() {}
    preserved_by noop() {}
  }
}
@*/

/*@
predicate lseg(struct node* from, struct node* to; list<struct node*> nodes, list<int> values) =
  from == to ?
    nodes == nil &*& values == nil
  :
    from != 0 &*& from->value |-> ?value &*& from->next |-> ?next &*& malloc_block_node(from) &*&
    lseg(next, to, ?nnodes, ?nvalues) &*& nodes == cons(from, nnodes) &*& values == cons(value, nvalues);

predicate queue(struct queue* q, predicate(list<int>) P) = msqueue_box(?id, q, P) &*& malloc_block_queue(q);
@*/

bool try_dequeue(struct queue* q, int* res)
  //@ requires queue(q, ?P) &*& integer(res, ?v);
  //@ ensures queue(q, P) &*& integer(res, ?nv) &*& result ? true : nv == v;
{
  ; // todo: fix bug
  //@ open queue(q, P);
  //@ assert msqueue_box(?id, q, P);
  //@ handle ha = create_handle msqueue_box_handle(id);
  // h = q->head
  /*@
  consuming_box_predicate msqueue_box(id, q, P)
  consuming_handle_predicate msqueue_box_handle(ha)
  perform_action noop()
  {
    @*/ struct node *h = atomic_load_pointer(&q->head); /*@
  }
  producing_handle_predicate was_head(h);
  @*/
  // n = h->next
  /*@
  consuming_box_predicate msqueue_box(id, q, P)
  consuming_handle_predicate was_head(ha, h)
  perform_action noop()
  {
    assert q->initial |-> ?initial;
    assert q->head |-> ?head;
    assert lseg(initial, 0, ?nodes, ?vs);
    lseg_distinct(initial, 0);
    lseg_split(initial, 0, h);
    assert lseg(initial, h, ?nodes1, _);
    assert lseg(h, 0, ?nodes2, _);
    @*/ struct node *n = atomic_load_pointer(&h->next); /*@
    open lseg(n, 0, _, _);
    lseg_merge(initial, h, 0);
    if(n != 0) {
      distinct_mem(nodes1, nodes2, h);
      distinct_mem(nodes1, nodes2, n);
      index_of_nth(nodes, n);
      index_of_append2(nodes1, nodes2, h);
      index_of_append2(nodes1, nodes2, n);
    }
  }
  producing_handle_predicate was_head_with_succ(h, n);
  @*/
  if(n == 0) {
    return false;
    //@ close queue(q, P);
    //@ leak was_head_with_succ(_, _, _, _);
  } else {
    // old = cas(&q->tail, h, n);
        /*@
    consuming_box_predicate msqueue_box(id, q, P)
    consuming_handle_predicate was_head_with_succ(ha, h, n)
    perform_action move_tail()
    { 
      assert q->initial |-> ?initial_;
      assert q->head |-> ?head_;
      assert q->tail |-> ?tail_;
      assert lseg(initial_, 0, ?nodes_, ?vs_);
      @*/ struct node* old_ = atomic_compare_and_set_pointer(&q->tail, h, n); /*@
      if(old_ != h) {
        index_of_nth(nodes_, tail_);
        index_of_nth(nodes_, h);
      }
    } producing_handle_predicate was_head_with_succ_not_tail(h, n); @*/
    // old = cas(&q->head, h, n)
    /*@
    consuming_box_predicate msqueue_box(id, q, P)
    consuming_handle_predicate was_head_with_succ_not_tail(ha, h, n)
    perform_action dequeue()
    {
      @*/ struct node* old = atomic_compare_and_set_pointer(&q->head, h, n); /*@
      
    } producing_handle_predicate was_head_with_succ(h, n); @*/
    // read h->value
    /*@
    consuming_box_predicate msqueue_box(id, q, P)
    consuming_handle_predicate was_head_with_succ(ha, h, n)
    perform_action noop()
    {
      assert q->initial |-> ?initial__;
      lseg_split(initial__, 0, h);
      @*/ int value = atomic_load_int(&h->value); /*@
      lseg_merge(initial__, h, 0);
    } producing_handle_predicate msqueue_box_handle(); 
    @*/
    *res = value;
    //@ leak msqueue_box_handle(ha, _);
    return true;
    //@ close queue(q, P);
  }
}