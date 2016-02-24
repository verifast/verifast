#ifndef CAT_H
#define CAT_H

//@ #include "io.gh"
#include "reader.h"
#include "writer.h"

/*@
predicate cat_io<u>(int queue_from_id, int queue_to_id, place<u> t1, list<int> text, place<u> t2) =
  split(t1, ?tr1, ?tw1)
    &*& reader_io(queue_from_id, tr1, 4, text, ?tr2)
    &*& writer_io(queue_to_id, tw1, text, ?tw2)
  &*& join(tr2, tw2, t2);
@*/

/**
 * Reads four numbers from queue_from, and write that to queue_to.
 * Buffering is allowed.
 */
void cat/*@<u> @*/(struct queue *queue_from, struct queue *queue_to);
/*@ requires
  [?f_queue_from]queue(?queue_id_from, queue_from)
  &*& [?f_queue_to]queue(?queue_id_to, queue_to)
  &*& cat_io<u>(queue_id_from, queue_id_to, ?t1, ?text, ?t2)
  &*& token(t1);
@*/
/*@ ensures
  [f_queue_from]queue(queue_id_from, queue_from)
  &*& [f_queue_to]queue(queue_id_to, queue_to)
  &*& token(t2);
@*/

#endif