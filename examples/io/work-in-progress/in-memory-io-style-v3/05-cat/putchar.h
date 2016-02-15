#ifndef PUTCHAR_H
#define PUTCHAR_H

#include "queue.h"
//@ #include "io.gh"
//@ #include <ghost_cells.gh>
/*@
predicate putchar_io(int queue_id, place t1, int c, place t2) =
  t2 == place_upd_progress(t1, append(place_progress(t1), {c}))
  &*& is_putchar_invar_updatable(?invar_updater, queue_id, t1, c, t2);


typedef lemma void putchar_invar_updatable(int queue_id, place t1, int c, place t2)();
  requires
    [1/2]ghost_cell<list<int> >(queue_id, ?buffer_contents)
    &*& token_without_invar(t1)
    &*& exists<predicate(;)>(?p) &*& p == place_io_invar(t1) &*& p();
  ensures
    [1/2]ghost_cell(queue_id, append(buffer_contents, {c}))
    &*& token_without_invar(t2)
    &*& p();
@*/

/**
 * Places one integer in the given queue.
 * 
 * This is blocking. If the queue is full, it waits until it is not full anymore.
 */
void putchar(struct queue *queue, int x);
/*@ requires
  [?f_queue]queue(?queue_id, queue)
  &*& putchar_io(queue_id, ?t1, x, ?t2)
  &*& token(t1);
@*/
/*@ ensures
  token(t2)
  &*& [f_queue]queue(queue_id, queue);
@*/


#endif