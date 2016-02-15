#ifndef GETCHAR_H
#define GETCHAR_H

//@ #include "io.gh"
//@ #include <ghost_cells.gh>
#include "prophecy.h"
#include "queue.h"

/*@
predicate getchar_io(int queue_id, place t1, int c, place t2) =
  t2 == place_upd_progress(t1, append(place_progress(t1), {c}))
  &*& prophecy(_, c)
  &*& is_getchar_invar_updatable(?invar_updater, queue_id, t1, c, t2);

typedef lemma void getchar_invar_updatable(int queue_id, place t1, int c, place t2)();
  requires
    [1/2]ghost_cell<list<int> >(queue_id, ?buffer_contents)
    &*& c == head(buffer_contents)
    &*& buffer_contents != nil
    &*& exists<predicate(;)>(?p) &*& p == place_io_invar(t1) &*& p()
    &*& token_without_invar(t1);
  ensures
    [1/2]ghost_cell(queue_id, tail(buffer_contents))
    &*& p()
    &*& token_without_invar(t2);
@*/


/**
 * Reads one integer from the given queue.
 * 
 * This is blocking. If the queue is empty, it waits until it is not empty anymore.
 */
int getchar(struct queue *queue);
//@ requires [?f_queue]queue(?queue_id, queue) &*& getchar_io(queue_id, ?t1, ?c, ?t2) &*& token(t1);
//@ ensures  [f_queue]queue(queue_id, queue) &*& token(t2) &*& result == c;

#endif
