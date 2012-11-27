#include "atomic_integer.h"
#include "threading.h"
#include "stdlib.h"

/*@
box_class prodcons(int xval, int* data, handle producer, handle consumer) {
  invariant exists<bool>(?in) &*& in ? integer(data, _) : true;
  
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

/*@ predicate_ctor I(box id, int* data)(int v) = 
  prodcons(id, v, data, ?producer, ?consumer);
@*/

void produce(int* x, int* data)
  //@ requires exists<box>(?id) &*& [?f]atomic_integer(x, I(id, data)) &*& integer(data, _) &*& ready_to_produce(?ha, id);
  //@ ensures exists<box>(id) &*& [f]atomic_integer(x, I(id, data)) &*& integer(data, _) &*& ready_to_produce(ha, id);
{
  int sent = 7;
  *data = sent;
  {
    /*@
    predicate_family_instance atomic_integer_set_pre(my_atomic_integer_set_lemma)(int v) = integer(data, _) &*& ready_to_produce(ha, id);
    predicate_family_instance atomic_integer_set_post(my_atomic_integer_set_lemma)(int old, int new) = is_producer(ha, id);
    lemma void my_atomic_integer_set_lemma()
      requires atomic_integer_set_pre(my_atomic_integer_set_lemma)(1) &*& I(id, data)(?old);
      ensures atomic_integer_set_post(my_atomic_integer_set_lemma)(old, 1) &*& I(id, data)(1);
    {
      open atomic_integer_set_pre(my_atomic_integer_set_lemma)(1);
      open I(id, data)(old);
      consuming_box_predicate prodcons(id, ?xval, data, ?producer, ?consumer)
      consuming_handle_predicate ready_to_produce(ha) 
      perform_action producer_release()
      {
        open exists(false);
        close exists(true);
      }
      producing_box_predicate prodcons(1, data, producer, consumer)
      producing_handle_predicate is_producer();
      close atomic_integer_set_post(my_atomic_integer_set_lemma)(old, 1);
      close I(id, data)(1);
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(my_atomic_integer_set_lemma) : atomic_integer_set_lemma(1, I(id, data))() { call();};
    //@ close atomic_integer_set_pre(my_atomic_integer_set_lemma)(1);
    atomic_integer_set(x, 1);
    //@ open atomic_integer_set_post(my_atomic_integer_set_lemma)(_, 1);
  }
  while(true) 
    //@ invariant [f]atomic_integer(x, I(id, data)) &*& is_producer(ha, id);
  {
    /*@
    predicate_family_instance atomic_integer_get_pre(my_atomic_integer_get_lemma)() = is_producer(ha, id);
    predicate_family_instance atomic_integer_get_post(my_atomic_integer_get_lemma)(int value) = value != 0 ? is_producer(ha, id) : ready_to_produce(ha, id) &*& integer(data, _);
    lemma void my_atomic_integer_get_lemma()
      requires atomic_integer_get_pre(my_atomic_integer_get_lemma)() &*& I(id, data)(?value);
      ensures atomic_integer_get_post(my_atomic_integer_get_lemma)(value) &*& I(id, data)(value);
    {
      open atomic_integer_get_pre(my_atomic_integer_get_lemma)();
      open I(id, data)(value);
      if(value != 0) {
      } else {
        consuming_box_predicate prodcons(id, ?xval, data, ?producer, ?consumer)
        consuming_handle_predicate is_producer(ha) 
        perform_action producer_get()
        {
          open exists(true);
          close exists(false);
        }
        producing_box_predicate prodcons(xval, data, producer, consumer)
        producing_handle_predicate ready_to_produce();
      }
      close I(id, data)(value);
      close atomic_integer_get_post(my_atomic_integer_get_lemma)(value);
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(my_atomic_integer_get_lemma) : atomic_integer_get_lemma(I(id, data))() { call();};
    //@ close atomic_integer_get_pre(my_atomic_integer_get_lemma)();
    int cval = atomic_integer_get(x);
    //@ open atomic_integer_get_post(my_atomic_integer_get_lemma)(cval);
    if(cval == 0)
      break;
  }
}


void consume(int* x, int* data)
  //@ requires exists<box>(?id) &*& [?f]atomic_integer(x, I(id, data)) &*& is_consumer(?ha, id);
  //@ ensures exists<box>(id) &*& [f]atomic_integer(x, I(id, data)) &*& is_consumer(ha, id);
{
  while(true) 
    //@ invariant [f]atomic_integer(x, I(id, data)) &*& is_consumer(ha, id);
  {
    /*@
    predicate_family_instance atomic_integer_get_pre(my_atomic_integer_get_lemma)() = is_consumer(ha, id);
    predicate_family_instance atomic_integer_get_post(my_atomic_integer_get_lemma)(int value) = value == 0 ? is_consumer(ha, id) : ready_to_consume(ha, id) &*& integer(data, _);
    lemma void my_atomic_integer_get_lemma()
      requires atomic_integer_get_pre(my_atomic_integer_get_lemma)() &*& I(id, data)(?value);
      ensures atomic_integer_get_post(my_atomic_integer_get_lemma)(value) &*& I(id, data)(value);
    {
      open atomic_integer_get_pre(my_atomic_integer_get_lemma)();
      open I(id, data)(value);
      if(value == 0) {
      } else {
        consuming_box_predicate prodcons(id, ?xval, data, ?producer, ?consumer)
        consuming_handle_predicate is_consumer(ha) 
        perform_action consumer_get()
        {
          open exists(true);
          close exists(false);
        }
        producing_box_predicate prodcons(xval, data, producer, consumer)
        producing_handle_predicate ready_to_consume();
      }
      close I(id, data)(value);
      close atomic_integer_get_post(my_atomic_integer_get_lemma)(value);
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(my_atomic_integer_get_lemma) : atomic_integer_get_lemma(I(id, data))() { call();};
    //@ close atomic_integer_get_pre(my_atomic_integer_get_lemma)();
    int cval = atomic_integer_get(x);
    //@ open atomic_integer_get_post(my_atomic_integer_get_lemma)(cval);
    if(cval != 0)
      break;
  }
  int read = *data;
  {
    /*@
    predicate_family_instance atomic_integer_set_pre(my_atomic_integer_set_lemma)(int v) = integer(data, _) &*& ready_to_consume(ha, id);
    predicate_family_instance atomic_integer_set_post(my_atomic_integer_set_lemma)(int old, int new) = is_consumer(ha, id);
    lemma void my_atomic_integer_set_lemma()
      requires atomic_integer_set_pre(my_atomic_integer_set_lemma)(0) &*& I(id, data)(?old);
      ensures atomic_integer_set_post(my_atomic_integer_set_lemma)(old, 0) &*& I(id, data)(0);
    {
      open atomic_integer_set_pre(my_atomic_integer_set_lemma)(0);
      open I(id, data)(old);
      consuming_box_predicate prodcons(id, ?xval, data, ?producer, ?consumer)
      consuming_handle_predicate ready_to_consume(ha) 
      perform_action consumer_release()
      {
        open exists(false);
        close exists(true);
      }
      producing_box_predicate prodcons(0, data, producer, consumer)
      producing_handle_predicate is_consumer();
      close atomic_integer_set_post(my_atomic_integer_set_lemma)(old, 0);
      close I(id, data)(0);
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(my_atomic_integer_set_lemma) : atomic_integer_set_lemma(0, I(id, data))() { call();};
    //@ close atomic_integer_set_pre(my_atomic_integer_set_lemma)(0);
    atomic_integer_set(x, 0);
    //@ open atomic_integer_set_post(my_atomic_integer_set_lemma)(_, 0);
  }
}

struct producer_info {
  int* x;
  int* data;
};

/*@
predicate_family_instance thread_run_data(producer)(struct producer_info* info) =
  info->x |-> ?x &*& info->data |-> ?data &*& malloc_block_producer_info(info) &*& exists<box>(?id) &*&
  [1/2]atomic_integer(x, I(id, data)) &*& integer(data, _) &*& ready_to_produce(?ha, id);
@*/

void consumer(int* x, int* data)
  //@ requires exists<box>(?id) &*& [?f]atomic_integer(x, I(id, data)) &*& is_consumer(?ha, id);
  //@ ensures false;
{
  while(true)
    //@ invariant exists<box>(id) &*& [f]atomic_integer(x, I(id, data)) &*& is_consumer(ha, id);
  {
    consume(x, data);
  }
}

void producer(struct producer_info* info) //@: thread_run
  //@ requires thread_run_data(producer)(info);
  //@ ensures true;
{
  //@ open thread_run_data(producer)(info);
  int* x = info->x;
  int* data = info->data;
  free(info);
  while(true)
    //@ invariant exists<box>(?id) &*& [?f]atomic_integer(x, I(id, data)) &*& integer(data, _) &*& ready_to_produce(?ha, id);
  {
    produce(x, data);
  }
}

int main() 
  //@ requires true;
  //@ ensures true;
{
  int x = 0;
  int data = 0;
  //@ close exists<bool>(false);
  //@ create_box id = prodcons(0, &data, producer0, consumer) and_handle producer0 = ready_to_produce() and_handle consumer = is_consumer();
  //@ close I(id, &data)(0);
  //@ create_atomic_integer(&x, I(id, &data));
  struct producer_info* info = malloc(sizeof(struct producer_info));
  if(info == 0) abort(); 
  info->x = &x;
  info->data = &data;
  //@ close exists<box>(id);
  //@ close thread_run_data(producer)(info);
  thread_start(producer, info);
  //@ close exists<box>(id);
  consumer(&x, &data);
  return 0;
}
