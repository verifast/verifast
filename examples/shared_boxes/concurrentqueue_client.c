#include "concurrentqueue.h"
#include "threading.h"
//@ #include "listex.gh"

/*@
fixpoint bool le(int x, int y) {
  return x <= y;
}

predicate queue_inv(list<int> vs) = forall(vs, (le)(0)) == true;

predicate_family_instance thread_run_pre(producer)(struct queue* q, any info) = 
  [1/2]queue(q, queue_inv);
  
predicate_family_instance thread_run_post(producer)(struct queue* q, any info) = 
  [1/2]queue(q, queue_inv);
@*/

void producer(struct queue* q) //@: thread_run_joinable
  //@ requires thread_run_pre(producer)(q, ?info);
  //@ ensures thread_run_post(producer)(q, info);
{
  //@ open thread_run_pre(producer)(q, info);
  for(int i = 0; i < 100; i++) 
    //@ invariant [1/2]queue(q, queue_inv) &*& 0 <= i && i <= 100;
  {
    /*@
    predicate_family_instance enqueue_pre(enqueue_lemma)() = true;
    predicate_family_instance enqueue_post(enqueue_lemma)() = true;
    lemma void enqueue_lemma()
      requires enqueue_pre(enqueue_lemma)() &*& queue_inv(?vs);
      ensures enqueue_post(enqueue_lemma)() &*& queue_inv(append(vs, cons(i, nil)));
    {
      open enqueue_pre(enqueue_lemma)();
      open queue_inv(vs);
      forall_append(vs, cons(i, nil), (le)(0));
      close queue_inv(append(vs, cons(i, nil)));
      close enqueue_post(enqueue_lemma)();
    }
    @*/  
    //@ produce_lemma_function_pointer_chunk(enqueue_lemma) : queue_enqueue(queue_inv, i)() { call();};
    //@ close enqueue_pre(enqueue_lemma)();
    enqueue(q, i);
    //@ open enqueue_post(enqueue_lemma)();
  }
  //@ close thread_run_post(producer)(q, info);
}

/*@
predicate_family_instance thread_run_pre(consumer)(struct queue* q, any info) = 
  [1/2]queue(q, queue_inv);
  
predicate_family_instance thread_run_post(consumer)(struct queue* q, any info) = 
  [1/2]queue(q, queue_inv);
@*/

void consumer(struct queue* q) //@: thread_run_joinable
  //@ requires thread_run_pre(consumer)(q, ?info);
  //@ ensures thread_run_post(consumer)(q, info);
{
  //@ open thread_run_pre(consumer)(q, info);
  int x;
  while(true)
    //@ invariant [1/2]queue(q, queue_inv) &*& x |-> _;
  {
    /*@
    predicate_family_instance try_dequeue_pre(try_dequeue_lemma)() = true;
    predicate_family_instance try_dequeue_post(try_dequeue_lemma)(bool success, int v) = ! success || le(0, v);
    lemma void try_dequeue_lemma()
      requires try_dequeue_pre(try_dequeue_lemma)() &*& queue_inv(?vs);
      ensures try_dequeue_post(try_dequeue_lemma)(vs != nil, ?res) &*& vs != nil ? res == head(vs) &*& queue_inv(tail(vs)) : queue_inv(vs);
    {
      open try_dequeue_pre(try_dequeue_lemma)();
      open queue_inv(vs);
      if(vs == nil) {
        close queue_inv(nil);
        close try_dequeue_post(try_dequeue_lemma)(false, 0);
      } else {
        switch(vs) { case nil: case cons(h, t): }
        close queue_inv(tail(vs));
        close try_dequeue_post(try_dequeue_lemma)(true, head(vs));
      }
    }
    @*/ 
    //@ produce_lemma_function_pointer_chunk(try_dequeue_lemma) : queue_try_dequeue(queue_inv)() { call();};
    //@ close try_dequeue_pre(try_dequeue_lemma)();
    bool dequeued = try_dequeue(q, &x);
    //@ open try_dequeue_post(try_dequeue_lemma)(_, _);
    if(dequeued) {
      assert 0 <= x;
    }
  }
}

int main() //@: main
  //@ requires true;
  //@ ensures true;
{
  //@ close queue_inv(nil);
  //@ close exists(queue_inv);
  struct queue* q = create_queue();
  if(q == 0) {
    //@ open queue_inv(nil);
    return 0;
  }
  //@ close thread_run_pre(producer)(q, unit);
  //struct thread* producer_thread = create_thread(producer);
  struct thread* producer_thread = thread_start_joinable(producer, q);
  //@ close thread_run_pre(consumer)(q, unit);
  struct thread* consumer_thread = thread_start_joinable(consumer, q);
  thread_join(producer_thread);
  thread_join(consumer_thread); 
  //@ open thread_run_post(producer)(q, _);
  //@ open thread_run_post(consumer)(q, _);
  // TODO: dispose queue (not possible yet because sequence from initial to head is not reachable anymore)
  //@ assume(false);
  return 0; //~allow_dead_code
}
