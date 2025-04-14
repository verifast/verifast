#ifndef CONCURRENTQUEUE_H
#define CONCURRENTQUEUE_H

struct queue;

/*@
predicate queue(struct queue* q, predicate(list<int>) I);
@*/

struct queue* create_queue();
  //@ requires exists<predicate(list<int> xs)>(?I) &*& I(nil);
  //@ ensures result == 0 ? I(nil) : queue(result, I);
  
/*@
predicate_family enqueue_pre(void* index)();
predicate_family enqueue_post(void* index)();

typedef lemma void queue_enqueue(predicate(list<int> vs) I, int x)();
  requires enqueue_pre(this)() &*& I(?vs);
  ensures enqueue_post(this)() &*& I(append(vs, cons(x, nil)));
@*/

void enqueue(struct queue* q, int x);
  //@ requires [?f]queue(q, ?I) &*& is_queue_enqueue(?lem, I, x) &*& enqueue_pre(lem)();
  //@ ensures [f]queue(q, I) &*& enqueue_post(lem)();

/*@
predicate_family try_dequeue_pre(void* index)();
predicate_family try_dequeue_post(void* index)(bool success, int res);

typedef lemma void queue_try_dequeue(predicate(list<int> vs) I)();
  requires try_dequeue_pre(this)() &*& I(?vs);
  ensures try_dequeue_post(this)(vs != nil, ?res) &*& vs != nil ? res == head(vs) &*& I(tail(vs)) : I(vs);
@*/

bool try_dequeue(struct queue* q, int* res);
  //@ requires [?f]queue(q, ?I) &*& *res |-> _ &*& is_queue_try_dequeue(?lem, I) &*& try_dequeue_pre(lem)();
  //@ ensures [f]queue(q, I) &*& try_dequeue_post(lem)(result, ?ret) &*& result ? *res |-> ret : *res |-> _;

#endif
