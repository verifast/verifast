#ifndef QUEUE_H
#define QUEUE_H
#include "../../../vstte2012/problem3/problem3.h" // Ring buffer
#include <threading.h>
//@ #include <ghost_cells.gh>

/*@
predicate_ctor queue_invariant(int queue_id, struct queue *queue)() =
  queue->ring_buffer |-> ?ring_buffer
  &*& ring_buffer(ring_buffer, _, ?buffer_contents)
  &*& [1/2]ghost_cell<list<int> >(queue_id, buffer_contents)
;

predicate queue(int queue_id, struct queue *queue;) = 
  queue->mutex |-> ?mutex
  &*& mutex(mutex, ((queue_invariant)(queue_id, queue)))
  &*& queue->cond_can_push |-> ?cond_can_push
  &*& mutex_cond(cond_can_push, mutex)
  &*& queue->cond_can_pop |-> ?cond_can_pop
  &*& mutex_cond(cond_can_pop, mutex)
  &*& malloc_block_queue(queue);
@*/
struct queue {
  struct mutex *mutex;
  struct ring_buffer *ring_buffer;
  struct mutex_cond *cond_can_push;
  struct mutex_cond *cond_can_pop;
};

struct queue *create_queue(int size);
//@ requires size > 0 && size * sizeof(int) < INT_MAX;
//@ ensures queue(?queue_id, result) &*& [1/2]ghost_cell<list<int> >(queue_id, {});

struct ring_buffer *queue_to_ring_buffer(struct queue *queue);
//@ requires queue(?family, queue);
//@ ensures ring_buffer(result, _, ?contents) &*& [1/2]ghost_cell<list<int> >(family, contents);

#endif
