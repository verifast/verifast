#include "atomics.h"
#include "threading.h"
#include "stdlib.h"

/*@
box_class prodcons(int* x, int* data, handle producer, handle consumer) {
  invariant integer(x, ?xval) &*& exists<bool>(?in) &*& in ? integer(data, _) : true;
  
  action consumer_get();
    requires actionHandle == consumer && !(xval != 0 && !in);
    ensures producer == old_producer && consumer == old_consumer && xval == old_xval && (old_xval == 0 ? in == old_in : in == false);
  
  action consumer_release();
    requires xval != 0 && in == false && actionHandle == consumer;
    ensures producer == old_producer && consumer == old_consumer && xval == 0 && in == true;
    
  action producer_get();
    requires actionHandle == producer && !(xval == 0 && !in);
    ensures producer == old_producer && consumer == old_consumer && xval == old_xval && (old_xval != 0 ? in == old_in : in == false);
  
  action producer_release();
    requires xval == 0 && in == false && actionHandle == producer;
    ensures producer == old_producer && consumer == old_consumer && xval != 0 && in == true;
    
  handle_predicate is_producer()
  {
    invariant predicateHandle == producer && !(xval == 0 && !in);
    
    preserved_by consumer_get() { }
    preserved_by consumer_release() { }
    preserved_by producer_get() { }
    preserved_by producer_release() { }
  }
  
  handle_predicate is_consumer()
  {
    invariant predicateHandle == consumer && !(xval != 0 && !in);
    
    preserved_by consumer_get() { }
    preserved_by consumer_release() { }
    preserved_by producer_get() { }
    preserved_by producer_release() { }
  }
  
  handle_predicate ready_to_produce()
  {
    invariant xval == 0 && in == false && predicateHandle == producer;
    
    preserved_by consumer_get() { }
    preserved_by consumer_release() { }
    preserved_by producer_get() { }
    preserved_by producer_release() { }
  }
  
  handle_predicate ready_to_consume()
  {
    invariant xval != 0 && in == false && predicateHandle == consumer;
    
    preserved_by consumer_get() { }
    preserved_by consumer_release() { }
    preserved_by producer_get() { }
    preserved_by producer_release() { }
  }
}
@*/

void produce(int* x, int* data)
  //@ requires [?f]prodcons(?id, x, data, ?producer, ?consumer) &*& integer(data, _) &*& ready_to_produce(producer, id);
  //@ ensures [f]prodcons(id, x, data, producer, consumer) &*& integer(data, _)  &*& ready_to_produce(producer, id);
{
  *data = 7;
  /*@
  consuming_box_predicate prodcons(id, x, data, producer, consumer)
  consuming_handle_predicate ready_to_produce(producer)
  perform_action producer_release() atomic
  { 
    @*/ atomic_set_int(x, 1); /*@
    open exists(false);
    close exists(true);
  }
  producing_handle_predicate is_producer();
  @*/
  while(true)
    //@ invariant [f]prodcons(id, x, data, producer, consumer) &*& is_producer(producer, id);
  {
    /*@
    consuming_box_predicate prodcons(id, x, data, producer, consumer)
    consuming_handle_predicate is_producer(producer)
    perform_action producer_get() atomic
    { 
      @*/ int val = atomic_load_int(x); /*@
      if(val == 0) {
        open exists(true);
        close exists(false);
      }
    }
    producing_handle_predicate if (val != 0) is_producer() else ready_to_produce(); 
    @*/
    if(val == 0) 
      break;
  }
}

struct producer_info {
  int* x;
  int* data;
};

/*@ predicate_family_instance thread_run_data(producer)(struct producer_info* info) =
  info->x |-> ?x &*& info->data |-> ?data &*&
  [1/2]prodcons(?id, x, data, ?producer, ?consumer) &*& integer(data, _) &*& ready_to_produce(producer, id);
@*/

void producer(struct producer_info* info) //@ : thread_run
  //@ requires thread_run_data(producer)(info);
  //@ ensures false;
{
  //@ open thread_run_data(producer)(info);
  int* x = info->x;
  int* data = info->data;
  while(true) 
    //@ invariant [1/2]prodcons(?id, x, data, ?producer, ?consumer) &*& integer(data, _) &*& ready_to_produce(producer, id);
  {
    produce(x, data);
  }
}

void consume(int* x, int* data)
  //@ requires [1/2]prodcons(?id, x, data, ?producer, ?consumer) &*& is_consumer(consumer, id);
  //@ ensures [1/2]prodcons(id, x, data, producer, consumer) &*& is_consumer(consumer, id);
{
  while(true) 
    //@ invariant [1/2]prodcons(id, x, data, producer, consumer) &*& is_consumer(consumer, id);
  {
    /*@
    consuming_box_predicate prodcons(id, x, data, producer, consumer)
    consuming_handle_predicate is_consumer(consumer)
    perform_action consumer_get() atomic
    { 
      @*/  int val = atomic_load_int(x); /*@
      if(val != 0) {
        open exists(true);
        close exists(false);
      }
    }
    producing_handle_predicate if (val == 0) is_consumer() else ready_to_consume(); 
    @*/
    if(val != 0)
      break;
  }
  int read = *data;
  /*@
  consuming_box_predicate prodcons(id, x, data, producer, consumer)
  consuming_handle_predicate ready_to_consume(consumer)
  perform_action consumer_release() atomic
  { 
    @*/ atomic_set_int(x, 0); /*@
    open exists(false);
    close exists(true);
  }
  producing_handle_predicate is_consumer();
  @*/
}

void consumer(int* x, int* data)
  //@ requires [1/2]prodcons(?id, x, data, ?producer, ?consumer) &*& is_consumer(consumer, id);
  //@ ensures false;
{
  while(true) 
    //@ invariant [1/2]prodcons(id, x, data, producer, consumer) &*& is_consumer(consumer, id);
  {
    consume(x, data);
  }
}

int main() 
  //@ requires true;
  //@ ensures true;
{
  int x = 0;
  int data = 0;
  //@ close exists(false);
  //@ create_box id = prodcons(&x, &data, producer0, consumer) and_handle producer0 = ready_to_produce() and_handle consumer = is_consumer();
  struct producer_info* info = malloc(sizeof(struct producer_info));
  if(info == 0)
    abort();
  info->x = &x;
  info->data = &data;
  //@ close thread_run_data(producer)(info);
  thread_start(producer, info);
  consumer(&x, &data);
  return 0;
}
  
