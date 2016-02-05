#include "queue.h"


struct queue *create_queue(int size)
//@ requires size > 0 && size * sizeof(int) < INT_MAX;
//@ ensures queue(?family, result) &*& [1/2]ghost_cell<list<int> >(family, {});
{
  struct queue *queue = malloc(sizeof(struct queue));
  if (queue == 0) abort();
  queue->ring_buffer = ring_buffer_create(size);
  if (queue->ring_buffer == 0) abort();
  //@ int family = create_ghost_cell<list<int> >({});
  //@ close queue_invariant(family, queue)();
  //@ close create_mutex_ghost_arg(queue_invariant(family, queue));
  struct  mutex *mutex = create_mutex();
  queue->mutex = mutex;
  //@ close create_mutex_cond_ghost_args(mutex);
  queue->cond_can_push = create_mutex_cond();
  //@ close create_mutex_cond_ghost_args(mutex);
  queue->cond_can_pop = create_mutex_cond();
  //@ close queue(family, queue);
  return queue;
}

struct ring_buffer *queue_to_ring_buffer(struct queue *queue)
//@ requires queue(?family, queue);
//@ ensures ring_buffer(result, _, ?contents) &*& [1/2]ghost_cell<list<int> >(family, contents);
{
  //@ open queue(_, _);
  mutex_dispose(queue->mutex);
  //@ open queue_invariant(family, queue)();
  mutex_cond_dispose(queue->cond_can_push);
  mutex_cond_dispose(queue->cond_can_pop);
  struct ring_buffer *ring_buffer = queue->ring_buffer;
  free(queue);
  return ring_buffer;
}


int queue_pop(struct queue *queue)
/*@ requires read2_io(?t1, ?family_buf, ?logic_invar, ?x, ?t2)
  &*& token(t1, ?family_io_read)
  &*& [?f]queue(family_buf, queue)
  &*& [?fm]ghost_mutex(?ghost_mutex, logic_invar);
@*/
/*@ ensures token(t2, family_io_read)
  &*& [f]queue(family_buf, queue)
  &*& result == x
  &*& [fm]ghost_mutex(ghost_mutex, logic_invar);
@*/
{
  //@ open queue(_,_);
  //@ assert [f]queue->mutex |-> ?mutex;
  mutex_acquire(queue->mutex);
  //@ open queue_invariant(family_buf, queue)();
   
  while (ring_buffer_is_empty(queue->ring_buffer))
  /*@ invariant
  
  // queue:
  [f]queue-> mutex|-> mutex
  &*& [f]queue->cond_can_push |-> ?cond_can_push
  &*& [f]mutex_cond(cond_can_push, mutex)
  &*& [f]queue->cond_can_pop |-> ?cond_can_pop
  &*& [f]mutex_cond(cond_can_pop, mutex)
  
  // invariant:
  &*& queue->ring_buffer |-> ?buffer
  &*& ring_buffer(buffer, _, ?buffer_contents)
  &*& [1/2]ghost_cell<list<int> >(family_buf, buffer_contents)
  
  &*& [fm]ghost_mutex(ghost_mutex, logic_invar)

  &*& mutex_held(mutex, (queue_invariant)(family_buf, queue), currentThread, f);
  @*/
  {
    //@ close queue_invariant(family_buf, queue)();
    mutex_cond_wait(queue->cond_can_pop, queue->mutex);
    //@ open queue_invariant(family_buf, queue)();
  }
  
  bool was_full = ring_buffer_is_full(queue->ring_buffer);
  
  int ret = ring_buffer_pop(queue->ring_buffer);
  
  if (was_full){
    mutex_cond_signal(queue->cond_can_push);
  }
  
  //@ open read2_io(t1, family_buf, logic_invar, x, t2);
  //@ assert is_can_queue_pop(?invar_updater, x, family_buf, logic_invar, t1, t2);
  //@ assert prophecy(?id, _);
  //@ close prophecy_assign_ghost_arg(id);
  prophecy_assign(ret);
  //@ invar_updater();
  //@ leak is_can_queue_pop(_, _, _, _, _, _);

  //@ close queue_invariant(family_buf, queue)();
  mutex_release(queue->mutex);
  //@ close [f]queue(family_buf, queue);
  
  return ret;
}

void queue_push(struct queue *queue, int x)
/*@ requires write1_io(?t1, ?family_buf1, ?logic_invar, x, ?t2)
  &*& token(t1, ?family_io_write)
  &*& [?f]queue(family_buf1, queue)
  &*& [?fm]ghost_mutex(?ghost_mutex, logic_invar);
@*/
/*@ ensures token(t2, family_io_write)
  &*& [f]queue(family_buf1, queue)
  &*& [fm]ghost_mutex(ghost_mutex, logic_invar);
@*/
{
  //@ open queue(_, _);
  //@ assert [f]queue->mutex |-> ?mutex;
  mutex_acquire(queue->mutex);
  //@ open queue_invariant(family_buf1, queue)();
   
  while (ring_buffer_is_full(queue->ring_buffer))
  /*@ invariant
  
  // queue:
  [f]queue-> mutex|-> mutex
  &*& [f]queue->cond_can_push |-> ?cond_can_push
  &*& [f]mutex_cond(cond_can_push, mutex)
  &*& [f]queue->cond_can_pop |-> ?cond_can_pop
  &*& [f]mutex_cond(cond_can_pop, mutex)
  
  // queue_invariant:
  &*& queue->ring_buffer |-> ?buffer
  &*& ring_buffer(buffer, _, ?buffer_contents)
  &*& [1/2]ghost_cell<list<int> >(family_buf1, buffer_contents)
  
  &*& [fm]ghost_mutex(ghost_mutex, logic_invar)

  &*& mutex_held(mutex, (queue_invariant)(family_buf1, queue), currentThread, f);
  @*/
  {
    //@ close queue_invariant(family_buf1, queue)();
    mutex_cond_wait(queue->cond_can_push, queue->mutex);
    //@ open queue_invariant(family_buf1, queue)();
  }
  
  bool was_empty = ring_buffer_is_empty(queue->ring_buffer);
  
  ring_buffer_push(queue->ring_buffer, x);
  
  if (was_empty){
    mutex_cond_signal(queue->cond_can_pop);
  }
  //@ open write1_io(t1, family_buf1, logic_invar, x, t2);
  //@ assert is_can_queue_push(?invar_updater, x, family_buf1, logic_invar, t1, t2);
  //@ invar_updater();
  //@ leak is_can_queue_push(_, _, _, _, _, _);

  //@ close queue_invariant(family_buf1, queue)();
  mutex_release(queue->mutex);
  //@ close [f]queue(family_buf1, queue);
}
