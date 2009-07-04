#include "stdlib.h"
#include "threading.h"
#include "lists.h"

struct producer {
  struct list* buffer;
  struct lock* lock;
};

struct consumer {
  struct list* buffer;
  struct lock* lock;
};

/*@
predicate_ctor list_ctor(struct list* list)()
  requires list(list, _);

predicate producer(struct producer* producer)
  requires producer->buffer |-> ?buffer &*& producer->lock |-> ?lock &*&
          [_]lock_permission(lock, list_ctor(buffer)) &*& malloc_block_producer(producer);

predicate_family_instance thread_run_data(produce)(void* data)
  requires producer(data);
@*/

struct producer* create_producer(struct list* buffer, struct lock* lock)
  //@ requires [_]lock_permission(lock, list_ctor(buffer));
  //@ ensures producer(result);
{
  struct producer* producer = malloc(sizeof(struct producer));
  if(producer == 0) { abort(); }
  producer->lock = lock;
  producer->buffer = buffer;
  close producer(producer);
  return producer;
}

void produce(void *data) //@ : thread_run
  //@ requires thread_run_data(produce)(data);
  //@ ensures thread_run_post(produce)(data);
{
  struct producer* producer = data;
  //@ open thread_run_data(produce)(data);
  while(true) 
    //@ invariant producer(producer);
  {
    //@ open producer(producer);
    struct lock* lock = producer->lock;
    struct list* buffer = producer->buffer;
    lock_acquire(lock);
    //@ open_lock_invariant();
    //@ open list_ctor(buffer)();
    list_add(buffer, 0);
    //@ close list_ctor(buffer)();
    //@ close_lock_invariant(list_ctor(buffer));
    lock_release(lock);
    //@ close producer(producer);
  }
}

/*@
predicate consumer(struct consumer* consumer)
  requires consumer->buffer |-> ?buffer &*& consumer->lock |-> ?lock &*&
          [_]lock_permission(lock, list_ctor(buffer)) &*& malloc_block_consumer(consumer);

predicate_family_instance thread_run_data(consume)(void* data)
  requires consumer(data);
@*/

struct consumer* create_consumer(struct list* buffer, struct lock* lock)
  //@ requires [_]lock_permission(lock, list_ctor(buffer));
  //@ ensures consumer(result);
{
  struct consumer* consumer = malloc(sizeof(struct consumer));
  if(consumer == 0) { abort(); }
  consumer->lock = lock;
  consumer->buffer = buffer;
  close consumer(consumer);
  return consumer;
}

void consume(void *data) //@ : thread_run
  //@ requires thread_run_data(consume)(data);
  //@ ensures thread_run_post(consume)(data);
{
  struct consumer* consumer = data;
  //@ open thread_run_data(consume)(data);
  while(true) 
    //@ invariant consumer(consumer);
  {
    //@ open consumer(consumer);
    struct lock* lock = consumer->lock;
    struct list* buffer = consumer->buffer;
    lock_acquire(lock);
    //@ open_lock_invariant();
    //@ open list_ctor(buffer)();
    int length = list_length(buffer);
    if(0 < length) {
      void* consumed = list_removeFirst(buffer);
    }
    //@ close list_ctor(buffer)();
    //@ close_lock_invariant(list_ctor(buffer));
    lock_release(lock);
    //@ close consumer(consumer);
  }
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct list* buffer = create_list();
  //@ close list_ctor(buffer)();
  //@ close_lock_invariant(list_ctor(buffer));
  struct lock* lock = create_lock();
  //@ split_lock_permission(lock);
  
  struct producer* producer = create_producer(buffer, lock);
  //@ close thread_run_data(produce)(producer);
  struct thread* t1 = thread_start(produce, producer);
  
  struct consumer* consumer = create_consumer(buffer, lock);
  //@ close thread_run_data(consume)(consumer);
  struct thread* t2 = thread_start(consume, consumer);
  
  dispose_thread_token(t1);
  dispose_thread_token(t2);
  return 0;
}
