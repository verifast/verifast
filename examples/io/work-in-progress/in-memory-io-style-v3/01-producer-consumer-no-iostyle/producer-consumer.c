#include <malloc.h>
#include <stdlib.h> // abort()
//@ #include <ghost_cells.gh>

/**
 * Motivating example for in-memory i/o.
 *
 * (Currently no i/o style here)
 */

#include "../../../../vstte2012/problem3/problem3.h" // Ring buffer
#include <threading.h>

struct buffer {
  struct ring_buffer *ring_buffer;
  struct mutex *mutex;
  struct mutex_cond *cond_can_push;
  struct mutex_cond *cond_can_pop;
};


/*@
predicate_ctor buffer_protected(struct buffer *buffer, int id_to_read, int id_to_write)() =
  buffer->ring_buffer |-> ?ring_buffer
  &*& ring_buffer(ring_buffer, ?size, ?contents)
  
  &*& [1/2]ghost_cell<list<int> >(id_to_read, ?to_read)
  &*& [1/2]ghost_cell<list<int> >(id_to_write, ?to_write)
  &*& exists<list<int> >(?read)
  &*& {1,2,3,4,5,6,7,8,9,10} == append(read, append(contents, to_write))
  &*& to_read == append(contents, to_write)
;

predicate buffer(struct buffer *buffer, int id_to_read, int id_to_write;) =
  buffer-> mutex|-> ?mutex
  &*& mutex(mutex, ((buffer_protected)(buffer, id_to_read, id_to_write)))
  &*& buffer->cond_can_push |-> ?cond_can_push
  &*& mutex_cond(cond_can_push, mutex)
  &*& buffer->cond_can_pop |-> ?cond_can_pop
  &*& mutex_cond(cond_can_pop, mutex)
  
  &*& malloc_block_buffer(buffer);
  
  
@*/

struct buffer *create_buffer(int size)
//@ requires true &*& size > 0 &*& size * sizeof(int) < INT_MAX &*& ghost_cell<list<int> >(?id_to_write, {1,2,3,4,5,6,7,8,9,10});
//@ ensures result == 0 ? ghost_cell(id_to_write, {1,2,3,4,5,6,7,8,9,10}) : buffer(result, ?id_to_read, id_to_write) &*& [1/2]ghost_cell(id_to_write, {1,2,3,4,5,6,7,8,9,10}) &*& [1/2]ghost_cell(id_to_read, {1,2,3,4,5,6,7,8,9,10});
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
  //@ int id_to_read = create_ghost_cell({1,2,3,4,5,6,7,8,9,10});
  //@ close create_mutex_ghost_arg(buffer_protected(buffer, id_to_read, id_to_write));
  //@ close exists<list<int> >(nil);
  //@ close buffer_protected(buffer, id_to_read, id_to_write)();
  buffer->mutex = create_mutex();
  //@ close create_mutex_cond_ghost_args(buffer->mutex);
  buffer->cond_can_push = create_mutex_cond();
  //@ close create_mutex_cond_ghost_args(buffer->mutex);
  buffer->cond_can_pop = create_mutex_cond();
  

  return buffer;
  //@ close buffer(buffer, id_to_read, id_to_write);
}

void buffer_dispose(struct buffer *buffer)
//@ requires buffer(buffer, ?id_to_read, ?id_to_write);
//@ ensures [1/2]ghost_cell<list<int> >(id_to_write, _) &*& [1/2]ghost_cell<list<int> >(id_to_read, _);
{
  //@ open buffer(_, _, _);
  mutex_cond_dispose(buffer->cond_can_push);
  mutex_cond_dispose(buffer->cond_can_pop);
  mutex_dispose(buffer->mutex);
  //@ open buffer_protected(buffer, id_to_read, id_to_write)();
  ring_buffer_dispose(buffer->ring_buffer);
  free(buffer);
}


/** add to end of queue */
void push(struct buffer *buffer, int x)
//@ requires [?f]buffer(buffer, ?id_to_read, ?id_to_write) &*& [1/2]ghost_cell<list<int> >(id_to_write, ?to_write) &*& head(to_write) == x &*& to_write != nil;
//@ ensures [f]buffer(buffer, id_to_read, id_to_write) &*& [1/2]ghost_cell(id_to_write, tail(to_write));
{
  //@ open buffer(buffer, _, _);
  //@ assert [f]buffer->mutex |-> ?mutex;
  mutex_acquire(buffer->mutex);
  //@ open buffer_protected(buffer, id_to_read, id_to_write)();
  while (ring_buffer_is_full(buffer->ring_buffer))
  /*@ invariant
      buffer->ring_buffer |-> ?ring_buffer
      &*& [f]buffer->mutex |-> mutex
      &*& ring_buffer(ring_buffer, ?size, ?contents)
      &*& [f]buffer->cond_can_push |-> ?cond_can_push
      &*& [f]mutex_cond(cond_can_push, mutex)
      &*& mutex_held(mutex, (buffer_protected)(buffer, id_to_read, id_to_write), currentThread, f)
      &*& [1/2]ghost_cell(id_to_read, ?to_read)
      &*& [1/2]ghost_cell(id_to_write, to_write)
      &*& [1/2]ghost_cell(id_to_write, to_write)
      &*& exists<list<int> >(?read)
      &*& {1,2,3,4,5,6,7,8,9,10} == append(read, append(contents, to_write))
      &*& to_read == append(contents, to_write)
      ;
      
  @*/
  {
    //@ close buffer_protected(buffer, id_to_read, id_to_write)();
    mutex_cond_wait(buffer->cond_can_push, buffer->mutex);
    //@ open buffer_protected(buffer, id_to_read, id_to_write)();
  }
  
  bool was_empty = ring_buffer_is_empty(buffer->ring_buffer);

  ring_buffer_push(buffer->ring_buffer, x);

  if (was_empty){
    mutex_cond_signal(buffer->cond_can_pop);
  }
  
  //@ assert to_write != nil;
  //@ assume (append(contents, to_write) == append(append(contents, cons(head(to_write),nil)), tail(to_write)));
  
  //@ ghost_cell_mutate(id_to_write, tail(to_write));

  //@ close buffer_protected(buffer, id_to_read, id_to_write)();
  mutex_release(buffer->mutex);
  //@ close [f]buffer(buffer, id_to_read, id_to_write);
}

/** read from beginning of queue (and remove that element) */
int pop(struct buffer *buffer)
//@ requires [?f]buffer(buffer, ?id_to_read, ?id_to_write) &*& [1/2]ghost_cell<list<int> >(id_to_read, ?to_read) &*& to_read != nil;
//@ ensures [f]buffer(buffer, id_to_read, id_to_write) &*&  [1/2]ghost_cell(id_to_read, tail(to_read)) &*& result == head(to_read);
{
  //@ open buffer(buffer, _, _);
  //@ assert [f]buffer->mutex |-> ?mutex;
  mutex_acquire(buffer->mutex);
  //@ open buffer_protected(buffer, id_to_read, id_to_write)();
  while (ring_buffer_is_empty(buffer->ring_buffer))
  /*@ invariant
      buffer->ring_buffer |-> ?ring_buffer
      &*& [f]buffer->mutex |-> mutex
      &*& ring_buffer(ring_buffer, ?size, ?contents)
      &*& [f]buffer->cond_can_pop |-> ?cond_can_pop
      &*& [f]mutex_cond(cond_can_pop, mutex)
      &*& [1/2]ghost_cell(id_to_read, to_read)
      &*& [1/2]ghost_cell(id_to_read, to_read)
      &*& [1/2]ghost_cell(id_to_write, ?to_write)
      &*& exists<list<int> >(?read)
      &*& {1,2,3,4,5,6,7,8,9,10} == append(read, append(contents, to_write))
      &*& to_read == append(contents, to_write)
      &*& mutex_held(mutex, (buffer_protected)(buffer, id_to_read, id_to_write), currentThread, f);
      
  @*/
  {
    //@ close buffer_protected(buffer, id_to_read, id_to_write)();
    mutex_cond_wait(buffer->cond_can_pop, buffer->mutex);
    //@ open buffer_protected(buffer, id_to_read, id_to_write)();
  }
  
  bool was_full = ring_buffer_is_full(buffer->ring_buffer);
  
  int x = ring_buffer_pop(buffer->ring_buffer);
  
  //@ assert contents != nil;
  //@ assert x == head(contents);
  //@ assume (x == head (append(contents, to_write)));
  
  if (was_full){
    mutex_cond_signal(buffer->cond_can_push);
  }
  
  //@ open exists(read);
  //@ close exists<list<int> >(append(read, cons(x, nil)));
  
  //@ assert contents != nil;
  //@ assume(append(read, append(contents, to_write)) == append(append(read, cons(head(contents), nil)), append(tail(contents), to_write)));
  
  //@ assume(tail(append(contents, to_write)) == append(tail(contents), to_write));
  
  //@ ghost_cell_mutate(id_to_read, tail(to_read));
  
  //@ close buffer_protected(buffer, id_to_read, id_to_write)();
  mutex_release(buffer->mutex);
  //@ close [f]buffer(buffer, id_to_read, id_to_write);
  return x;
}

/*@ predicate_family_instance thread_run_pre(producer)(struct buffer *buffer, any p) =
  [1/2]buffer(buffer, ?id_to_read, ?id_to_write) &*& [1/2]ghost_cell(id_to_write, {1,2,3,4,5,6,7,8,9,10})
  &*& p == pair(id_to_read, id_to_write);
@*/
/*@ predicate_family_instance thread_run_post(producer)(struct buffer *buffer, any p) =
  [1/2]buffer(buffer, ?id_to_read, ?id_to_write) &*& [1/2]ghost_cell<list<int> >(id_to_write, {})
  &*& p == pair(id_to_read, id_to_write);
@*/

void producer(struct buffer *buffer) //@ : thread_run_joinable
//@ requires thread_run_pre(producer)(buffer, ?info) &*& lockset(currentThread, nil);
//@ ensures thread_run_post(producer)(buffer, info) &*& lockset(currentThread, nil);
{
  int x = 1;
  //@ open thread_run_pre(producer)(buffer, info);
  
  // let's save on proving list properties by unrolling the loop. 
  push(buffer, x);
  x++;
  
  push(buffer, x);
  x++;
  
  push(buffer, x);
  x++;
  
  push(buffer, x);
  x++;
  
  push(buffer, x);
  x++;
  
  push(buffer, x);
  x++;
  
  push(buffer, x);
  x++;
  
  push(buffer, x);
  x++;
  
  push(buffer, x);
  x++;

  push(buffer, x);
  x++;
  
  //@ close thread_run_post(producer)(buffer, info);
}

int consumer(struct buffer *buffer, int count)
//@ requires [?f]buffer(buffer, ?id_to_read, ?id_to_write) &*& [1/2]ghost_cell(id_to_read, {1,2,3,4,5,6,7,8,9,10});
//@ ensures [f]buffer(buffer, id_to_read, id_to_write) &*& [1/2]ghost_cell<list<int> >(id_to_read, {}) &*& result == 55;
{
  int i;
  int sum = 0;
  
  int pop_result = pop(buffer);
  sum = sum + pop_result;
  
  pop_result = pop(buffer);
  sum = sum + pop_result;
  
  pop_result = pop(buffer);
  sum = sum + pop_result;
  
  pop_result = pop(buffer);
  sum = sum + pop_result;
  
  pop_result = pop(buffer);
  sum = sum + pop_result;
  
  pop_result = pop(buffer);
  sum = sum + pop_result;
  
  pop_result = pop(buffer);
  sum = sum + pop_result;
  
  pop_result = pop(buffer);
  sum = sum + pop_result;
  
  pop_result = pop(buffer);
  sum = sum + pop_result;
  
  pop_result = pop(buffer);
  sum = sum + pop_result;
  
  return sum;
}
/*
struct cat_data{
  struct buffer *buffer1;
  struct buffer *buffer2;
};
*/
/* @
predicate cat_data(struct cat_data *cat_data) =
  cat_data->buffer1 |-> ?buffer1 
  &*& cat_data->buffer2 |-> ?buffer2
  &*& [?f1]buffer(buffer1)
  &*& [?f2]buffer(buffer2)
  &*& malloc_block_cat_data(cat_data);
@*/

// @ predicate_family_instance thread_run_data(cat)(struct cat_data *cat_data) = cat_data(cat_data);

/*
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
*/

int main()
//@ requires true;
//@ ensures result == 55;
{
  //@ int id_to_write = create_ghost_cell({1,2,3,4,5,6,7,8,9,10});
  struct buffer *buffer = create_buffer(64);
  //@ assert [1/2]ghost_cell(id_to_write, _) &*& [1/2]ghost_cell(?id_to_read, _);
  if (buffer == 0){
    abort();
  }
  //@ split_fraction buffer(buffer, _, _) by 1/2;
  //@ close thread_run_pre(producer)(buffer, pair(id_to_read, id_to_write));
  struct thread *thread = thread_start_joinable(producer, buffer);
  int result = consumer(buffer, 100);
  thread_join(thread);
  //@ open thread_run_post(producer)(buffer, pair(id_to_read, id_to_write));
  //@ assert [1/2]buffer(buffer, id_to_read, id_to_write) &*& [1/2]buffer(buffer, id_to_read, id_to_write);
  //@ merge_fractions buffer(buffer, id_to_read, id_to_write);
  buffer_dispose(buffer);
  return result;
  //@ ghost_cell_leak(id_to_read);
  //@ ghost_cell_leak(id_to_write);
}
