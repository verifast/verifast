#include "getchar.h"

/**
 * Reads one integer from the given queue.
 * 
 * This is blocking. If the queue is empty, this function waits until the queue is not empty anymore.
 */
int getchar/*@<u> @*/(struct queue *queue)
//@ requires [?f_queue]queue(?queue_id, queue) &*& getchar_io<u>(queue_id, ?t1, ?c, ?t2) &*& token(t1);
//@ ensures  [f_queue]queue(queue_id, queue) &*& token(t2) &*& result == c;
{
  //@ open [f_queue]queue(_,_);
  //@ assert [f_queue]queue->mutex |-> ?mutex; // bind mutex so we know it won't change.
  mutex_acquire(queue->mutex);
  //@ open queue_invariant(queue_id, queue)();
  
  //@ open token(t1);
   
  while (ring_buffer_is_empty(queue->ring_buffer))
  /*@ invariant
    // from queue:
    [f_queue]queue->mutex |-> mutex
    &*& [f_queue]queue->cond_can_pop |-> ?cond_can_pop
    &*& [f_queue]mutex_cond(cond_can_pop, mutex)
    
    // from the mutex:
    &*& queue->ring_buffer |-> ?buffer
    &*& ring_buffer(buffer, _, ?buffer_contents)
    &*& [1/2]ghost_cell<list<int> >(queue_id, buffer_contents)
    &*& mutex_held(mutex, (queue_invariant)(queue_id, queue), currentThread, f_queue);
  @*/
  {
    //@ close queue_invariant(queue_id, queue)();
    mutex_cond_wait(queue->cond_can_pop, queue->mutex);
    //@ open queue_invariant(queue_id, queue)();
  }
  
  bool was_full = ring_buffer_is_full(queue->ring_buffer);
  
  //@ open getchar_io(queue_id, t1, c, t2);
  
  int ret = ring_buffer_pop(queue->ring_buffer);
  prophecy_assign(ret);
  
  if (was_full){
    mutex_cond_signal(queue->cond_can_push);
  }
  
  /*@
  {
    predicate pre() =
      [1/2]ghost_cell<list<int> >(queue_id, buffer_contents)
      &*& c == head(buffer_contents)
      &*& token_without_invar(t1)
      &*& is_getchar_invar_updatable(?invar_updater, queue_id, t1, c, t2);
    predicate post() =
      [1/2]ghost_cell(queue_id, tail(buffer_contents))
      &*& token_without_invar(t2);
    
    close pre();
    produce_lemma_function_pointer_chunk(empty_lemma) : ghost_mutex_critical_section_t(place_io_invar(t1), pre, post)()
    {
      open pre();
      assert is_getchar_invar_updatable(?invar_updater, queue_id, t1, c, t2);
      close exists(place_io_invar(t1));
      open token_without_invar(t1);
      invar_updater();
      close token_without_invar(t2);
      close post();
      leak is_getchar_invar_updatable(_, _, _, _, _);
      call();
    }
    {
      ghost_mutex_use(place_mutex(t1), pre, post);
    }
    open post();
  }
  @*/
  
  //@ close queue_invariant(queue_id, queue)();
  mutex_release(queue->mutex);
  //@ close [f_queue]queue(queue_id, queue);
  
  return ret;
}

