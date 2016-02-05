#ifndef QUEUE_H
#define QUEUE_H
#include <threading.h>
#include "../../../../vstte2012/problem3/problem3.h" // Ring buffer
#include <stdlib.h> // abort()
//@ #include <ghost_cells.gh>
#include "io.h"
#include "prophecy.h"
//@ #include "ghost_mutex.gh"


/*@
predicate_ctor queue_invariant(int family, struct queue *queue)() =
  queue->ring_buffer |-> ?ring_buffer
  &*& ring_buffer(ring_buffer, _, ?buffer_contents)
  &*& [1/2]ghost_cell<list<int> >(family, buffer_contents)
;

predicate queue(int family, struct queue *queue;) = 
  queue->mutex |-> ?mutex
  &*& mutex(mutex, ((queue_invariant)(family, queue)))
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
//@ ensures queue(?family, result) &*& [1/2]ghost_cell<list<int> >(family, {});

struct ring_buffer *queue_to_ring_buffer(struct queue *queue);
//@ requires queue(?family, queue);
//@ ensures ring_buffer(result, _, ?contents) &*& [1/2]ghost_cell<list<int> >(family, contents);


/*@
predicate write1_io(place t1, int family_buf1, predicate() logic_invar, int c, place t2) =
  t2 == place_io(t1, c)
  &*& is_can_queue_push(?f, c, family_buf1, logic_invar, t1, t2);

predicate read2_io(place t1, int family2_buf, predicate() logic_invar, int c, place t2) =
  t2 == place_io(t1, c)
  &*& is_can_queue_pop(?f, c, family2_buf, logic_invar, t1, t2)
  &*& prophecy(_, c);


typedef lemma void can_queue_push(int c, int family1_buf, predicate() logic_invar, place t1, place t2)();
  requires
    [?f]ghost_mutex(?mutex, logic_invar)
    &*& [1/2]ghost_cell<list<int> >(family1_buf, ?buffer1_contents)
    &*& token(t1, ?family_io);
  ensures
    [f]ghost_mutex(mutex, logic_invar)
    &*& [1/2]ghost_cell<list<int> >(family1_buf, append(buffer1_contents,{c}))
    &*& token(t2, family_io);

typedef lemma void can_queue_pop(int c, int family2_buf, predicate() logic_invar, place t1, place t2)();
  requires
    [?fm]ghost_mutex(?ghost_mutex, logic_invar)
    &*& [1/2]ghost_cell<list<int> >(family2_buf, ?buffer2_contents)
    &*& buffer2_contents != nil
    &*& c == head(buffer2_contents)
    &*& token(t1, ?family_io);
  ensures
    [fm]ghost_mutex(ghost_mutex, logic_invar)
    &*& token(t2, family_io)
    &*& [1/2]ghost_cell<list<int> >(family2_buf, tail(buffer2_contents))
    &*& c == head(buffer2_contents);
@*/

int queue_pop(struct queue *queue);
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

void queue_push(struct queue *queue, int x);
/*@ requires write1_io(?t1, ?family_buf1, ?logic_invar, x, ?t2)
  &*& token(t1, ?family_io_write)
  &*& [?f]queue(family_buf1, queue)
  &*& [?fm]ghost_mutex(?ghost_mutex, logic_invar);
@*/
/*@ ensures token(t2, family_io_write)
  &*& [f]queue(family_buf1, queue)
  &*& [fm]ghost_mutex(ghost_mutex, logic_invar);
@*/


#endif
