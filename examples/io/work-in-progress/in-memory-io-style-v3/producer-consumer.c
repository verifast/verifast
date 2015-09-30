#include <malloc.h>
#include <stdlib.h> // abort()

/**
 * Motivating example for in-memory i/o.
 *
 * (Currently only memory-safety is verified to test condition variables)
 */

#include "../../../vstte2012/problem3/problem3.h" // Ring buffer
#include <threading.h>

struct buffer {
  struct ring_buffer *ring_buffer;
  struct mutex *mutex;
  struct mutex_cond *cond_can_push;
  struct mutex_cond *cond_can_pop;
};

/*@

predicate_ctor buffer_protected(struct buffer *buffer)() =
  buffer->ring_buffer |-> ?ring_buffer
  &*& ring_buffer(ring_buffer, ?size, ?contents)  
;

predicate buffer(struct buffer *buffer) =
  buffer-> mutex|-> ?mutex
  &*& mutex(mutex, ((buffer_protected)(buffer)))
  &*& buffer->cond_can_push |-> ?cond_can_push
  &*& mutex_cond(cond_can_push, mutex)
  &*& buffer->cond_can_pop |-> ?cond_can_pop
  &*& mutex_cond(cond_can_pop, mutex)

  &*& malloc_block_buffer(buffer);
  
  
@*/

struct buffer *setup(int size)
//@ requires true &*& size > 0 &*& size * sizeof(int) < INT_MAX;
//@ ensures result == 0 ? emp : buffer(result);
{
  struct buffer *buffer = malloc(sizeof(struct buffer));
  if (buffer == 0){
    return 0;
  }
  struct ring_buffer *ring_buffer = ring_buffer_create(size);
  if (ring_buffer == 0){
    free(buffer);
    return 0;
  }
  buffer->ring_buffer = ring_buffer;
  
  //@ close create_mutex_ghost_arg(buffer_protected(buffer));
  //@ close buffer_protected(buffer)();
  buffer->mutex = create_mutex();
  //@ close create_mutex_cond_ghost_args(buffer->mutex);
  buffer->cond_can_push = create_mutex_cond();
  //@ close create_mutex_cond_ghost_args(buffer->mutex);
  buffer->cond_can_pop = create_mutex_cond();
  

  return buffer;
  //@ close buffer(buffer);
}


/** add to end of queue */
void push(struct buffer *buffer, int x)
//@ requires [?f]buffer(buffer);
//@ ensures [f]buffer(buffer);
{
  //@ open buffer(buffer);
  //@ assert [f]buffer->mutex |-> ?mutex;
  mutex_acquire(buffer->mutex);
  //@ open buffer_protected(buffer)();
  while (ring_buffer_is_full(buffer->ring_buffer))
  /*@ invariant
      buffer->ring_buffer |-> ?ring_buffer
      &*& [f]buffer->mutex |-> mutex
      &*& ring_buffer(ring_buffer, ?size, ?contents)
      &*& [f]buffer->cond_can_push |-> ?cond_can_push
      &*& [f]mutex_cond(cond_can_push, mutex)
      &*& mutex_held(mutex, (buffer_protected)(buffer), currentThread, f);
      
  @*/
  {
    //@ close buffer_protected(buffer)();
    mutex_cond_wait(buffer->cond_can_push, buffer->mutex);
    //@ open buffer_protected(buffer)();
  }
  
  bool was_empty = ring_buffer_is_empty(buffer->ring_buffer);
  
  ring_buffer_push(buffer->ring_buffer, x);
  
  if (was_empty){
    mutex_cond_signal(buffer->cond_can_pop);
  }
  
  //@ close buffer_protected(buffer)();
  mutex_release(buffer->mutex);
  //@ close [f]buffer(buffer);
}

/** read from beginning of queue (and remove that element) */
int pop(struct buffer *buffer)
//@ requires [?f]buffer(buffer);
//@ ensures [f]buffer(buffer);
{
  //@ open buffer(buffer);
  //@ assert [f]buffer->mutex |-> ?mutex;
  mutex_acquire(buffer->mutex);
  //@ open buffer_protected(buffer)();
  while (ring_buffer_is_empty(buffer->ring_buffer))
  /*@ invariant
      buffer->ring_buffer |-> ?ring_buffer
      &*& [f]buffer->mutex |-> mutex
      &*& ring_buffer(ring_buffer, ?size, ?contents)
      &*& [f]buffer->cond_can_pop |-> ?cond_can_pop
      &*& [f]mutex_cond(cond_can_pop, mutex)
      &*& mutex_held(mutex, (buffer_protected)(buffer), currentThread, f);
      
  @*/
  {
    //@ close buffer_protected(buffer)();
    mutex_cond_wait(buffer->cond_can_pop, buffer->mutex);
    //@ open buffer_protected(buffer)();
  }
  
  bool was_full = ring_buffer_is_full(buffer->ring_buffer);
  
  int x = ring_buffer_pop(buffer->ring_buffer);
  
  if (was_full){
    mutex_cond_signal(buffer->cond_can_push);
  }
  
  //@ close buffer_protected(buffer)();
  mutex_release(buffer->mutex);
  //@ close [f]buffer(buffer);
  return x;
}

//@ predicate_family_instance thread_run_data(producer)(struct buffer *buffer) = [?f]buffer(buffer);

void producer(struct buffer *buffer) //@ : thread_run
//@ requires thread_run_data(producer)(buffer);
//@ ensures false;
{
  int x = 0;
  //@ open thread_run_data(producer)(buffer);
  while(true)
  //@ invariant [?f]buffer(buffer);
  {
    push(buffer, x);
    if (x == INT_MAX){
      x = 0;
    }else{
      x++;
    }
  }
}

int consumer(struct buffer *buffer, int count)
//@ requires [?f]buffer(buffer);
//@ ensures [f]buffer(buffer);
{
  int i;
  int sum = 0;
  for (i = 0; i < count ; i++)
  //@ invariant [f]buffer(buffer);
  {
    int pop_result = pop(buffer);
    bool has_overflow = (pop_result > 0 && sum > INT_MAX - pop_result)
                     || (pop_result < 0 && sum < INT_MIN - pop_result);
    if (has_overflow){
      abort();
    }
    sum = sum + pop_result;
  }
  return sum;
}

struct cat_data{
  struct buffer *buffer1;
  struct buffer *buffer2;
};

/*@
predicate cat_data(struct cat_data *cat_data) =
  cat_data->buffer1 |-> ?buffer1 
  &*& cat_data->buffer2 |-> ?buffer2
  &*& [?f1]buffer(buffer1)
  &*& [?f2]buffer(buffer2)
  &*& malloc_block_cat_data(cat_data);
@*/

//@ predicate_family_instance thread_run_data(cat)(struct cat_data *cat_data) = cat_data(cat_data);

void cat(struct cat_data *cat_data) //@ : thread_run
//@ requires thread_run_data(cat)(cat_data);
//@ ensures false; // non-terminating
{
  //@ open thread_run_data(cat)(cat_data);
  while(true)
  //@ invariant cat_data(cat_data);
  {
    //@ open cat_data(cat_data);
    int pop_result = pop(cat_data->buffer1);
    push(cat_data->buffer2, pop_result);
    //@ close cat_data(cat_data);
  }
}

int main()
//@ requires true;
//@ ensures true;
{
  struct buffer *buffer = setup(64);
  if (buffer == 0){
    return -1;
  }
  //@ split_fraction buffer(buffer) by 1/2;
  //@ close thread_run_data(producer)(buffer);
  thread_start(producer, buffer);
  int result = consumer(buffer, 100);
  // this is a bit dirty...
  //@ leak [1/2]buffer(buffer);
  return result;
}

int main_with_cat()
//@ requires true;
//@ ensures true;
{
  struct buffer *buffer1 = setup(16);
  struct buffer *buffer2 = setup(48);
  struct cat_data *cat_data = malloc(sizeof(struct cat_data));
  if (buffer1 == 0 || buffer2 == 0 || cat_data == 0){
    abort();
  }
  
  //@ split_fraction buffer(buffer1) by 1/2;
  //@ close thread_run_data(producer)(buffer1);
  thread_start(producer, buffer1);
  
  cat_data->buffer1 = buffer1;
  cat_data->buffer2 = buffer2;
  //@ split_fraction buffer(buffer2) by 1/2;
  //@ close cat_data(cat_data);
  //@ close thread_run_data(cat)(cat_data);
  thread_start(cat, cat_data);
  
  int result = consumer(buffer2, 100);
  // this is a bit dirty...
  //@ leak [1/2]buffer(buffer2);
  return result;
}
