/*
Michael-Scott queue (without memory reclamation)
*/

#include "stdlib.h"
#include "atomics.h"
#include "concurrentqueue.h"

struct node {
  int value;
  struct node* next;
};

struct queue {
  //@ struct node* initial;
  struct node* head;
  struct node* tail;
};

/**
 * AUXILIARY LEMMAS
 */ 

/*@
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

lemma_auto(nth(i, append(xs, ys)))
void nth_append_auto<t>(list<t> xs, list<t> ys, int i)
  requires 0 <= i && i < length(xs);
  ensures nth(i, xs) == nth(i, append(xs, ys));
{
  nth_append(xs, ys, i);
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

lemma void drop_one_more<t>(list<t> xs, int i)
  requires 0 <= i &*& i <= length(xs) - 1;
  ensures drop(i, xs) == cons(nth(i, xs), drop(i + 1, xs));
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i != 0) {
        drop_one_more(t, i - 1);
      }
  }
}

lemma void drop_nth_index_of<t>(list<t> vs, int i)
  requires 0 <= i && i < length(vs);
  ensures head(drop(i , vs)) == nth(i, vs);
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(i == 0) {

      } else {
        drop_nth_index_of(t, i - 1);
      }
  }
}

lemma_auto void drop_append_l<t>(list<t> xs, list<t> ys, int i)
  requires 0 <= i && i <= length(xs);
  ensures drop(i, append(xs, ys)) == append(drop(i, xs), ys);
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i == 0) {
      } else {
        drop_append_l(t, ys, i - 1);
      }
  }
}
 @*/

/*@
box_class msqueue_box(struct queue* q, predicate(list<int>) I) {
  invariant q->initial |-> ?initial &*& q->head |-> ?head &*& q->tail |-> ?tail &*& lseg(initial, 0, ?nodes, ?vs) &*&
            mem(head, nodes) == true &*& mem(tail, nodes) == true &*& index_of(head, nodes) <= index_of(tail, nodes) &*&
            length(nodes) - 2 <= index_of(tail, nodes) &*& I(drop(index_of(head, nodes) + 1, vs)) &*& malloc_block_queue(q) &*&
            //derived
            length(nodes) == length(vs);
            
  action enqueue(struct node* new_node, int x);
    requires true;
    ensures initial == old_initial && head == old_head && tail == old_tail && 
            ((nodes == old_nodes && vs == old_vs) || (nodes == append(old_nodes, cons(new_node, nil)) && vs == append(old_vs, cons(x, nil))));
  
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
  
  /**
   DEQUEUE
  **/
  
  handle_predicate was_head(struct node* h) {
    invariant mem(h, nodes) == true && index_of(h, nodes) <= index_of(head, nodes); 
    
    preserved_by enqueue(new_node, x) { }
    preserved_by dequeue() { }
    preserved_by move_tail() { }
    preserved_by noop() { }
  }
  
  handle_predicate was_head_with_succ(struct node* h, struct node* n) extends was_head {
    invariant n != 0 && index_of(h, nodes) < length(nodes) - 1 && n == nth(index_of(h, nodes) + 1, nodes) && index_of(h, nodes) + 1 == index_of(n, nodes);
              
    preserved_by enqueue(new_node, x) {
        index_of_append(old_nodes, {new_node}, h);
        index_of_append(old_nodes, {new_node}, n);
    }
    preserved_by dequeue() { }
    preserved_by move_tail() { }
    preserved_by noop() { }
  }
  
  handle_predicate was_head_with_succ_not_tail(struct node* h, struct node* n) extends was_head_with_succ {
    invariant index_of(h, nodes) < index_of(tail, nodes);
              
    preserved_by enqueue(new_node, x) { }
    preserved_by dequeue() { }
    preserved_by move_tail() { }
    preserved_by noop() { }
  }
  
  handle_predicate is_good_node(struct node* n, int v) {
    invariant mem(n, nodes) == true && nth(index_of(n, nodes), vs) == v;

              
    preserved_by enqueue(new_node, x) {
        index_of_append(old_nodes, {new_node}, n);
        nth_append_auto(vs, {x}, index_of(n, old_nodes));
    }
    preserved_by dequeue() { }
    preserved_by move_tail() { }
    preserved_by noop() { }
  }
  
  /**
   ENQUEUE
  **/
  
  handle_predicate was_tail(struct node* t) {
    invariant mem(t, nodes) == true && index_of(t, nodes) <= index_of(tail, nodes); 
    
    preserved_by enqueue(new_node, x) { }
    preserved_by dequeue() { }
    preserved_by move_tail() { }
    preserved_by noop() { }
  }
  
  handle_predicate was_tail_with_succ(struct node* t, struct node* n) extends was_tail {
    invariant (n != 0 ? 
                index_of(t, nodes) < length(nodes) - 1 && n == nth(index_of(t, nodes) + 1, nodes) && index_of(t, nodes) + 1 == index_of(n, nodes)
              :
                true
              );
              
    preserved_by enqueue(new_node, x) {
        if (n != 0) {
            index_of_append(old_nodes, {new_node}, t);
            mem_nth(index_of(t, old_nodes) + 1, old_nodes);
            index_of_append(old_nodes, {new_node}, n);
        }
    }
    preserved_by dequeue() { }
    preserved_by move_tail() { }
    preserved_by noop() { }
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
    
lemma void lseg_nodes_values(struct node* from, struct node* to)
  requires lseg(from, to, ?nodes, ?vs);
  ensures lseg(from, to, nodes, vs) &*& length(nodes) == length(vs);
{
  open lseg(from, to, nodes, vs);
  if(from != to) {
    lseg_nodes_values(from->next, to);
  }
}

lemma void lseg_split(struct node* from, struct node* to, struct node* n)
  requires lseg(from, to, ?nodes, ?vs) &*& mem(n, nodes) == true;
  ensures lseg(from, n, ?nodes1, ?vs1) &*& lseg(n, to, ?nodes2, ?vs2) &*& n != to &*& append(nodes1, nodes2) == nodes && append(vs1, vs2) == vs &*& length(vs1) == index_of(n, nodes);
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

predicate queue(struct queue* q, predicate(list<int>) I) = msqueue_box(?id, q, I);
@*/

struct queue* create_queue()
  //@ requires exists<predicate(list<int> xs)>(?I) &*& I(nil);
  //@ ensures result == 0 ? I(nil) : queue(result, I);
{
  //@ open exists(I);
  struct queue* q = malloc(sizeof(struct queue));
  if(q == 0) {
    return 0;
  }
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) {
    free(q);
    return 0;
  }
  n->value = 0;
  n->next = 0;
  q->head = n;
  q->tail = n;
  //@ q->initial = n;
  return q;
  //@ create_box boxId = msqueue_box(q, I); 
  //@ close queue(q, I);
}

void enqueue(struct queue* q, int x)
  //@ requires [?f]queue(q, ?I) &*& is_queue_enqueue(?lem, I, x) &*& enqueue_pre(lem)();
  //@ ensures [f]queue(q, I) &*& enqueue_post(lem)();
{
  struct node* new_node = malloc(sizeof(struct node));
  if(new_node == 0) abort();
  new_node->value = x;
  new_node->next = 0;
  while(true)
    //@ invariant [f]queue(q, I) &*& is_queue_enqueue(lem, I, x) &*& enqueue_pre(lem)() &*& new_node->value |-> x &*& new_node->next |-> 0 &*& malloc_block_node(new_node);
  {
    //@ open queue(q, I);
    //@ assert [f]msqueue_box(?id, q, I);
    //@ handle ha = create_handle msqueue_box_handle(id);
    /*@
    consuming_box_predicate msqueue_box(id, q, I)
    consuming_handle_predicate msqueue_box_handle(ha)
    perform_action noop()
    {
      @*/ struct node *t = atomic_load_pointer(&q->tail); /*@
    }
    producing_handle_predicate was_tail(ha, t);
    @*/
    
    /*@
    consuming_box_predicate msqueue_box(id, q, I)
    consuming_handle_predicate was_tail(ha, t)
    perform_action enqueue(new_node, x)
    {
      assert lseg(?initial, 0, ?nodes, ?vs);
      lseg_distinct(initial, 0);
      lseg_split(initial, 0, t);
      assert lseg(initial, t, ?nodes1, ?vs1);
      assert lseg(t, 0, ?nodes2, ?vs2);
      int tdata = t->value;
      @*/ struct node *n = atomic_compare_and_set_pointer(&t->next, 0, new_node); /*@
      if(n == 0) {
        open lseg(0, 0, _, _);
        append_assoc(vs1, cons(tdata, nil), cons(x, nil));
        append_assoc(nodes1, cons(t, nil), cons(new_node, nil));
        lem();
      } else {
        open lseg(n, _, _, _);
        distinct_mem(nodes1, nodes2, t);
        distinct_mem(nodes1, nodes2, n);
        index_of_nth(nodes, n);
        index_of_append2(nodes1, nodes2, t);
        index_of_append2(nodes1, nodes2, n);
      }
      lseg_merge(initial, t, 0);
    }
    producing_handle_predicate was_tail_with_succ(ha, t, n);
    @*/
    if(n == 0) {
      //@ close [f]queue(q, I);
      //@ leak is_queue_enqueue(_, _, _);
      //@ leak was_tail_with_succ(_, _, _, _);
      return;
    }
    
    /*@
    consuming_box_predicate msqueue_box(id, q, I)
    consuming_handle_predicate was_tail_with_succ(ha, t, n)
    perform_action move_tail()
    {
    @*/ struct node* old = atomic_compare_and_set_pointer(&q->tail, t, n); /*@
    };
    @*/
    //@ close [f]queue(q, I);
  }
}

bool try_dequeue(struct queue* q, int* res)
  //@ requires [?f]queue(q, ?I) &*& integer(res, ?v) &*& is_queue_try_dequeue(?lem, I) &*& try_dequeue_pre(lem)();
  //@ ensures [f]queue(q, I) &*& integer(res, ?nv) &*& try_dequeue_post(lem)(result, ?ret) &*& result ? ret == nv : true;
{
  //@ open [f]queue(q, I);
  //@ assert [f]msqueue_box(?id, q, I);
  //@ handle ha = create_handle msqueue_box_handle(id);
  while(true)
    //@ invariant [f]msqueue_box(id, q, I) &*& integer(res, v) &*& is_queue_try_dequeue(lem, I) &*& try_dequeue_pre(lem)() &*& msqueue_box_handle(ha, id);
  {
    // h = q->head
    /*@
    consuming_box_predicate msqueue_box(id, q, I)
    consuming_handle_predicate msqueue_box_handle(ha)
    perform_action noop()
    {
      @*/ struct node *h = atomic_load_pointer(&q->head); /*@
    }
    producing_handle_predicate was_head(ha, h);
    @*/
    // n = h->next
    /*@
    consuming_box_predicate msqueue_box(id, q, I)
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
      } else {
        distinct_mem(nodes1, nodes2, h);
        index_of_append2(nodes1, nodes2, h);
        lseg_nodes_values(initial, 0);
        lem();
        leak is_queue_try_dequeue(_, _);
      }
    }
    producing_handle_predicate if(n == 0) msqueue_box_handle(ha) else was_head_with_succ(ha, h, n);
    @*/
    if(n == 0) {
      return false;
      //@ close [f]queue(q, I);
      //@ leak msqueue_box_handle(_, _);
    } else {
      // old = cas(&q->tail, h, n);
          /*@
      consuming_box_predicate msqueue_box(id, q, I)
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
      } producing_handle_predicate was_head_with_succ_not_tail(ha, h, n); @*/
      // old = cas(&q->head, h, n)
      /*@
      consuming_box_predicate msqueue_box(id, q, I)
      consuming_handle_predicate was_head_with_succ_not_tail(ha, h, n)
      perform_action dequeue()
      {
        assert lseg(?theinitial, 0, ?thenodes, ?thevalues);
        @*/ struct node* old = atomic_compare_and_set_pointer(&q->head, h, n); /*@
        int ret;
        if(old == h) {
          lem();
          lseg_nodes_values(theinitial, 0);
          drop_one_more(thevalues, index_of(h, thenodes) + 1);
          leak is_queue_try_dequeue(_, _);
          assert try_dequeue_post(_)(_, ?retv);
          ret = retv;
          assert ret == head(drop(index_of(h, thenodes) + 1, thevalues));
          drop_nth_index_of(thevalues, index_of(h, thenodes) + 1);
        } else {
          ret = 0;
        }
      } producing_handle_predicate if (old == h) is_good_node(ha, n, ret) else msqueue_box_handle(ha); @*/
      if(old == h) {
        // read n->value
        /*@
        consuming_box_predicate msqueue_box(id, q, I)
        consuming_handle_predicate is_good_node(ha, n, ret)
        perform_action noop()
        {
          assert q->initial |-> ?initial__;
          assert q->head |-> ?head__;
          assert q->tail |-> ?tail__;
          assert lseg(_, _, ?lnodes, ?lvs);
          lseg_nodes_values(initial__, 0);
          lseg_split(initial__, 0, n);
           assert lseg(initial__, n, ?lnodes1, ?lvs1);
           assert lseg(n, 0, ?lnodes2, ?lvs2);
          @*/ int value = atomic_load_int(&n->value); /*@
          lseg_merge(initial__, n, 0);
          
          assert ret == nth(index_of(n, lnodes), lvs);
          assert value == nth(0, lvs2);
          nth_append_r(lvs1, lvs2, index_of(n, lnodes) - length(lvs1));
          assert value == ret;
        }; 
        @*/
        *res = value;
        return true;
        //@ close [f]queue(q, I);
      }
    }
  }
}
